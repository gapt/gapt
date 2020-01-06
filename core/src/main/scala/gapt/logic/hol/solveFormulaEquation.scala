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
import gapt.utils.NameGenerator

/**
 * Uses the DLS algorithm to find a witness for formula equations of the form
 * ?X_1 ... ?X_n φ where φ is a first order formula and X_1,...,X_n are second order variables.
 *
 * The return value is a substitution of the occurring second order variables such that
 * applying the substitution to φ gives a first order formula which is equivalent to
 * ?X_1 ... ?X_n φ.
 *
 * Does not yet work for formulas where a positive occurrence of the second order variable is
 * inside the scope of an existential quantifier which is itself inside the scope of an
 * universal quantifier.
 */
object solveFormulaEquation {

  private def vectorEq( expressionsA: Iterable[Expr], expressionsB: Iterable[Expr] ): Formula = {
    And( expressionsA.zip( expressionsB ) map { case ( a, b ) => Eq( a, b ) } )
  }

  private def freshArgumentVariables(
    secondOrderVariable: Var,
    disjuncts:           Set[HOLSequent] ): List[FOLVar] = secondOrderVariable match {
    case Var( _, FunctionType( To, inputTypes ) ) if inputTypes.forall( _ == Ti ) => {
      val blackListVariableNames = disjuncts.flatMap( variables( _ ) ).map( _.name )
      val argumentName = secondOrderVariable.name.toLowerCase()
      new NameGenerator( blackListVariableNames )
        .freshStream( argumentName )
        .map( FOLVar( _ ) )
        .take( inputTypes.length )
        .toList
    }
  }

  /**
   * Returns the succedent of the implication in Ackermann's lemma which is equivalent to the given
   * positive formula
   */
  private def positiveOccurrenceWitness(
    formula:             Formula,
    secondOrderVariable: Var,
    argumentVariables:   Seq[FOLVar] ): Formula = formula match {
    case _ if !formula.contains( secondOrderVariable ) => Top()
    case Atom( variable, arguments ) if variable == secondOrderVariable =>
      vectorEq( argumentVariables, arguments )
    case Neg( alpha ) =>
      Neg( positiveOccurrenceWitness( alpha, secondOrderVariable, argumentVariables ) )
    case And( alpha, beta ) =>
      Or(
        positiveOccurrenceWitness( alpha, secondOrderVariable, argumentVariables ),
        positiveOccurrenceWitness( beta, secondOrderVariable, argumentVariables ) )
    case Or.nAry( disjuncts ) if disjuncts.length >= 2 => {
      val partialWitnesses = disjuncts.map(
        disjunct => {
          val witness = positiveOccurrenceWitness(
            disjunct,
            secondOrderVariable,
            argumentVariables )
          val substitution = Substitution( secondOrderVariable, Abs( argumentVariables, witness ) )
          ( applySubstitutionBetaReduced( substitution, disjunct ), witness )
        } )
      disjunctiveWitnessCombination( partialWitnesses )
    }
    case All( variable, innerFormula ) => Ex(
      variable,
      positiveOccurrenceWitness( innerFormula, secondOrderVariable, argumentVariables ) )

    // todo: handle Ex by skolemization
  }

  private def positiveOccurrencesWitness(
    secondOrderVariable: Var,
    disjunct:            HOLSequent ): Expr = {
    val argumentVariables = freshArgumentVariables( secondOrderVariable, Set( disjunct ) )
    val witness = positiveOccurrenceWitness(
      And( disjunct.succedent ),
      secondOrderVariable,
      argumentVariables )
    Abs( argumentVariables, simplify( witness ) )
  }

  def witnessSubstitutions(
    secondOrderVariable: Var,
    disjunct:            HOLSequent ): ( Substitution, Substitution ) = {
    val witnessA = positiveOccurrencesWitness( secondOrderVariable, disjunct )
    ( Substitution( secondOrderVariable, witnessA ), Substitution() )
  }

  private def applySubstitutionBetaReduced(
    substitution: Substitution,
    formula:      Formula ): Formula = {
    BetaReduction.betaNormalize( substitution( formula ) )
  }

  private def disjunctiveWitnessCombination(
    disjunctsWithWitnesses: Iterable[( Formula, Formula )] ): Formula = {
    And( disjunctsWithWitnesses.toList.inits.toList.init.map( initList => {
      val ( disjunct, witness ) = initList.last
      val negatedInit = initList.init.map( element => Neg( element._1 ) )
      val antecedent = And( negatedInit :+ disjunct )
      Imp( antecedent, witness )
    } ) )
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

  private def distributeTopLevelConjunctionsOverDisjunctions(
    formula: Formula ): Set[Formula] = formula match {
    case And.nAry( conjuncts ) => {
      val disjunctsInConjuncts = conjuncts.map( { case Or.nAry( disjuncts ) => disjuncts } )
      crossProduct( disjunctsInConjuncts ).map( And.apply( _ ) ).toSet
    }
  }

  private def moveQuantifiers( formula: Formula ): Formula = {
    moveExistentialQuantifiersUp( moveUniversalQuantifiersDown( formula ) )
  }

  private object FirstOrderExBlock {
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

  private def polarizedConjuncts(
    formula:  Formula,
    variable: Var ): Option[HOLSequent] = formula match {
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
      case FirstOrderExBlock( variables, innerFormula ) => {
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
    case Ex( secondOrderVariable @ Var( _, FunctionType( To, _ :: _ ) ), innerFormula ) => {
      apply( innerFormula ).flatMap( {
        case ( substitution, firstOrderPart ) =>
          val firstOrderFormula = applySubstitutionBetaReduced( substitution, firstOrderPart )
          preprocess( secondOrderVariable, firstOrderFormula )
            .map( {
              case ( existentialVariables, disjuncts ) => {
                val partialSubstitutions = disjuncts.map(
                  disjunct => ( disjunct, witnessSubstitutions( secondOrderVariable, disjunct ) ) )
                val variables = freshArgumentVariables( secondOrderVariable, disjuncts )
                val witnessCombination = disjunctiveWitnessCombination( partialSubstitutions.map( {
                  case ( disjunct, ( positiveSubstitution, _ ) ) => {
                    ( applySubstitutionBetaReduced( positiveSubstitution, And( disjunct.antecedent ) ),
                      BetaReduction.betaNormalize(
                        Apps( positiveSubstitution.map.get( secondOrderVariable ).get, variables ) ) match {
                          case f: Formula => f
                        } )
                  }
                } ) )
                val witnessCombinationRelation = Abs( variables, simplify( witnessCombination ) )
                val substitutionMap = substitution.map + ( secondOrderVariable -> witnessCombinationRelation )
                val updatedSubstitution = Substitution( substitutionMap )
                ( updatedSubstitution, firstOrderFormula )
              }
            } )
      } )
    }
    case _ => Success( ( Substitution(), formula ) )
  }
}
