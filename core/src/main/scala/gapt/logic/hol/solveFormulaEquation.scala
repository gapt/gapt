package gapt.logic.hol
import gapt.expr.formula._
import gapt.expr.ty._
import scala.util.{ Success, Try, Failure }
import gapt.expr.formula.prop.PropFormula
import gapt.expr.formula.hol.containsHOQuantifier
import gapt.expr.formula.hol.containsQuantifier
import gapt.expr.containedNames
import gapt.expr.formula.hol.HOLPosition
import gapt.expr.subst._
import gapt.expr._
import gapt.proofs._
import gapt.expr.util.rename
import gapt.expr.util.freeVariables
import gapt.expr.util.variables
import gapt.expr.formula.hol.BinaryConnective
import gapt.expr.formula.constants.AndC
import gapt.expr.formula.fol.FOLVar
import gapt.logic.Polarity
import gapt.provers.escargot.impl.DiscrTree.Variable
import gapt.proofs.Sequent

/**
 * Uses the DLS algorithm to find a witness for formula equations
 * of the form ?X φ where φ is a first order formula and X is a second order variable
 *
 * The return value is a substitution of the occurring second order variables such that
 * applying the substitution to φ yields a first order formula which is equivalent to ?X φ
 *
 * At the moment φ may only be a quantifier free formula
 * and the quantified relation must be unary
 */
object solveFormulaEquation {

  private def partialWitness( positiveOccurrences: Iterable[Formula] ): Formula = {
    Or( positiveOccurrences.map( {
      // todo: handle multiple arguments
      // todo: unique name for unbound variable "x"
      // todo: identify quantifier variable
      case Atom( _, args ) => Eq( FOLVar( "x" ), args.head )
    } ) )
  }

  private def substituteWitness( formula: Formula, variable: Var, witness: Formula ): Expr = {
    val substitutionMap = Map( variable -> Abs( FOLVar( "x" ), witness ) )
    normalize( Substitution( substitutionMap )( formula ) )
  }

  private def completeWitness(
    disjuncts:          Set[HOLSequent],
    quantifierVariable: Var ): Formula = {
    val witnessClauses = for {
      disjunct <- disjuncts
      ( positiveOccurrences, nonPositiveOcurrences ) = ( disjunct.succedent, disjunct.antecedent )
      witnessPart = partialWitness( positiveOccurrences )
      substituteWitnessPart = substituteWitness( _, quantifierVariable, witnessPart )
    } yield ( witnessPart, And( nonPositiveOcurrences.map( substituteWitnessPart ) ) )

    val witnessConjuncts = witnessClauses.toList.inits.toList.init.map( initList => {
      val ( witnessPart, nonPositiveOcurrence ) = initList.last
      val negatedInit = initList.init.map( element => Neg( element._2 ) )
      val antecedent = And( negatedInit :+ nonPositiveOcurrence )
      Imp( antecedent, witnessPart )
    } )

    And( witnessConjuncts )
  }

  private def replaceVariablesWithNewVariable[T](
    variablesInFormulas: Iterable[( Var, Formula )] ): ( Var, Iterable[Formula] ) =
    variablesInFormulas match {
      case ( headVariable: Var, _ ) :: _ => {
        val blackListVariables = variablesInFormulas.flatMap( x => variables( x._2 ) )
        val newVariable = rename( headVariable, blackListVariables )
        val substitute = Substitution( _: Var, newVariable )( _: Formula )
        ( newVariable, variablesInFormulas.map( x => substitute( x._1, x._2 ) ) )
      }
      case _ => throw new Exception( "list must be non-empty" )
    }

  private object AndOr {
    def unapply(
      formula: Formula ): Option[( Formula, Formula, MonoidalBinaryPropConnectiveHelper )] =
      formula match {
        case And( alpha, beta ) => Some( ( alpha, beta, And ) )
        case Or( alpha, beta )  => Some( ( alpha, beta, Or ) )
        case _                  => None
      }
  }

  private def isFreeIn( variable: Var, formula: Formula ): Boolean = {
    freeVariables( formula ).contains( variable )
  }

  private def moveUniversalQuantifiersDown( formula: Formula ): Formula = formula match {
    case All( variable, And( alpha, beta ) ) =>
      And(
        moveUniversalQuantifiersDown( All( variable, alpha ) ),
        moveUniversalQuantifiersDown( All( variable, beta ) ) )

    case All( variable, AndOr( alpha, beta, connective ) ) if !isFreeIn( variable, alpha ) =>
      connective(
        moveUniversalQuantifiersDown( alpha ),
        moveUniversalQuantifiersDown( All( variable, beta ) ) )

    case All( variable, AndOr( beta, alpha, connective ) ) if !isFreeIn( variable, alpha ) =>
      moveUniversalQuantifiersDown( All( variable, connective( alpha, beta ) ) )

    case Quant( variable, alpha, pol ) =>
      Quant( variable, moveUniversalQuantifiersDown( alpha ), pol )

    case AndOr( alpha, beta, connective ) =>
      connective(
        moveUniversalQuantifiersDown( alpha ),
        moveUniversalQuantifiersDown( beta ) )

    case _ => formula
  }

  private def moveExistentialQuantifiersUp( formula: Formula ): Formula = formula match {
    case Or( Ex( variableAlpha, alpha ), Ex( variableBeta, beta ) ) => {
      val ( newVariable, substitutedFormulas ) = replaceVariablesWithNewVariable(
        List(
          ( variableAlpha, alpha ),
          ( variableBeta, beta ) ) )
      Ex( newVariable, moveExistentialQuantifiersUp( Or( substitutedFormulas ) ) )
    }

    case AndOr( alpha, Ex( variable, beta ), connective ) => {
      val ( newVariable, substitutedFormulas ) = replaceVariablesWithNewVariable(
        List(
          ( variable, alpha ),
          ( variable, beta ) ) )
      Ex( newVariable, moveExistentialQuantifiersUp( Or( substitutedFormulas ) ) )
    }

    case AndOr( Ex( variable, beta ), alpha, connective ) =>
      moveExistentialQuantifiersUp( connective( alpha, Ex( variable, beta ) ) )

    case Quant( variable, alpha, pol ) =>
      Quant( variable, moveExistentialQuantifiersUp( alpha ), pol )

    case AndOr( alpha, beta, connective ) => {
      val movedAlpha = moveExistentialQuantifiersUp( alpha )
      val movedBeta = moveExistentialQuantifiersUp( beta )
      if ( movedAlpha != alpha || movedBeta != beta )
        moveExistentialQuantifiersUp( connective( movedAlpha, movedBeta ) )
      else
        formula
    }

    case _ => formula
  }

  private def crossProduct[T]( lists: List[List[T]] ): List[List[T]] = lists match {
    case Nil          => List( Nil )
    case head :: rest => for { x <- head; y <- crossProduct( rest ) } yield x :: y
  }

  private def distributeTopLevelConjunctionsOverDisjunctions( formula: Formula ): Set[Formula] = formula match {
    case And.nAry( conjuncts ) => {
      val disjunctsInConjuncts = conjuncts.map( { case Or.nAry( disjuncts ) => disjuncts } )
      crossProduct( disjunctsInConjuncts ).map( And.apply( _ ) ).toSet
    }
  }

  private def moveQuantifiers( formula: Formula ): Formula = {
    moveExistentialQuantifiersUp( moveUniversalQuantifiersDown( formula ) )
  }

  private object FirstOrderExPrefix {
    def apply( existentialVariables: List[FOLVar], formula: Formula ): Formula =
      existentialVariables match {
        case Nil              => formula
        case variable :: rest => Ex( variable, apply( rest, formula ) )
      }

    def unapply( formula: Formula ): Option[( List[FOLVar], Formula )] = formula match {
      case Ex( variable: FOLVar, innerFormula ) => {
        val ( variables, extractedFormula ) = unapply( innerFormula ).get
        Some( variable :: variables, extractedFormula )
      }
      case _ => Some( Nil, formula )
    }
  }

  private def polaritiesWithRespectTo(
    formula:  Formula,
    variable: Var,
    polarity: Polarity = Polarity.Positive ): Set[Polarity] = formula match {
    case Atom( atomVariable, _ ) if atomVariable == variable => Set( polarity )
    case Neg( alpha ) =>
      polaritiesWithRespectTo( alpha, variable, !polarity )
    case AndOr( alpha, beta, _ ) =>
      polaritiesWithRespectTo( alpha, variable, polarity ) ++
        polaritiesWithRespectTo( beta, variable, polarity )
    case Quant( _, alpha, _ ) => polaritiesWithRespectTo( alpha, variable, polarity )
    case _                    => Set()
  }

  private def uniquePolarityWithRespectTo( formula: Formula, variable: Var ): Option[Polarity] = {
    val polarities = polaritiesWithRespectTo( formula, variable )
    if ( polarities.size <= 1 )
      Some( polarities.headOption.getOrElse( Polarity.Positive ) )
    else
      None
  }

  private def polarizedConjuncts( formula: Formula, variable: Var ): Option[HOLSequent] = formula match {
    case And.nAry( conjuncts ) => {
      val conjunctsWithPolarities = conjuncts
        .map( conjunct => ( conjunct, uniquePolarityWithRespectTo( conjunct, variable ) ) )

      if ( conjunctsWithPolarities.exists( { case ( _, polarity ) => polarity == None } ) )
        None
      else
        Some( Sequent( conjunctsWithPolarities.map( f => ( f._1, f._2.get ) ) ) )
    }
  }

  def preprocess(
    secondOrderVariable: Var,
    formula:             Formula ): Try[( List[FOLVar], Set[HOLSequent] )] = {
    val nnf = toNNF( formula )
    moveQuantifiers( nnf ) match {
      case FirstOrderExPrefix( variables, innerFormula ) => {
        val disjuncts = distributeTopLevelConjunctionsOverDisjunctions( innerFormula )

        val polarizedConjunctsInDisjuncts = disjuncts
          .map( polarizedConjuncts( _, secondOrderVariable ) )
        if ( polarizedConjunctsInDisjuncts.exists( _.isEmpty ) )
          Failure(
            new Exception( "formula cannot be separated into positive and negative conjuncts" ) )
        else
          Success( ( variables, polarizedConjunctsInDisjuncts.map( _.get ) ) )
      }
    }
  }

  def apply( formula: Formula ): Try[( Substitution, Formula )] = formula match {
    case Ex( variable @ Var( _, _ ->: To ), innerFormula ) => {
      apply( innerFormula ).flatMap( {
        case ( substitution, firstOrderPart ) =>
          val firstOrderFormula = BetaReduction.betaNormalize( substitution( firstOrderPart ) )
          preprocess( variable, firstOrderFormula )
            .map( {
              case ( existentialVariables, disjuncts ) => {
                val witness = completeWitness( disjuncts, variable )
                val newSubstitution = variable -> Abs( FOLVar( "x" ), witness )
                val substitutionMap = substitution.map + newSubstitution
                val updatedSubstitution = Substitution( substitutionMap )
                ( updatedSubstitution, firstOrderFormula )
              }
            } )
      } )
    }
    case _ => Success( ( Substitution(), formula ) )
  }
}
