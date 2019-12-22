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
import gapt.proofs.HOLClause
import gapt.expr.util.rename
import gapt.expr.util.freeVariables
import gapt.expr.util.variables
import gapt.expr.formula.hol.BinaryConnective
import gapt.expr.formula.constants.AndC
import gapt.expr.formula.fol.FOLVar
import gapt.logic.Polarity
import gapt.provers.escargot.impl.DiscrTree.Variable

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

  def extractFirstOrderPart( formula: Formula ): Formula = formula match {
    case Quant( Var( _, FunctionType( To, _ ) ), innerFormula, _ ) => extractFirstOrderPart( innerFormula )
    case _ => formula
  }

  private def partialWitness( positiveOccurrences: Iterable[Formula] ): Formula = {
    Or( positiveOccurrences.map( {
      // todo: handle multiple arguments
      // todo: unique name for unbound variable "x"
      case Atom( _, args ) => Eq( FOLVar( "x" ), args.head )
    } ) )
  }

  private def substituteWitness( formula: Formula, variable: Var, witness: Formula ): Expr = {
    val substitutionMap = Map( variable -> Abs( FOLVar( "x" ), witness ) )
    normalize( Substitution( substitutionMap )( formula ) )
  }

  private def completeWitness( splitDisjunctions: Set[( List[Formula], List[Formula] )], quantifierVariable: Var ): Formula = {
    val witnessClauses = for {
      clause <- splitDisjunctions
      ( positiveOccurrences, nonPositiveOcurrences ) = clause
      witnessPart = partialWitness( positiveOccurrences )
    } yield ( witnessPart, And( nonPositiveOcurrences.map( substituteWitness( _, quantifierVariable, witnessPart ) ) ) )

    val witnessConjuncts = witnessClauses.toList.inits.toList.init.map( initList => {
      val ( witnessPart, nonPositiveOcurrence ) = initList.last
      Imp( And( initList.init.map( element => Neg( element._2 ) ) :+ nonPositiveOcurrence ), witnessPart )
    } )

    And( witnessConjuncts )
  }

  private def withNewVariable[T]( variable: Var, formulaAlpha: Formula, formulaBeta: Formula, transform: ( Var, Formula, Formula ) => T ): T = {
    val newVariable = rename( variable, variables( formulaAlpha ) ++ variables( formulaBeta ) )
    val substitution = Substitution( variable, newVariable )
    transform( newVariable, substitution( formulaAlpha ), substitution( formulaBeta ) )
  }

  private object AndOr {
    def unapply( formula: Formula ): Option[( Formula, Formula, ( Formula, Formula ) => Formula )] = formula match {
      case And( alpha, beta ) => Some( ( alpha, beta, And.apply ) )
      case Or( alpha, beta )  => Some( ( alpha, beta, Or.apply ) )
      case _                  => None
    }
  }

  private def moveUniversalQuantifiersDown( formula: Formula ): Formula = formula match {
    case All( variable, And( alpha, beta ) ) => And( moveUniversalQuantifiersDown( All( variable, alpha ) ), moveUniversalQuantifiersDown( All( variable, beta ) ) )
    case All( variable, AndOr( alpha, beta, connective ) ) if !freeVariables( alpha ).contains( variable ) => connective( moveUniversalQuantifiersDown( alpha ), moveUniversalQuantifiersDown( All( variable, beta ) ) )
    case All( variable, AndOr( beta, alpha, connective ) ) if !freeVariables( alpha ).contains( variable ) => connective( moveUniversalQuantifiersDown( All( variable, beta ) ), moveUniversalQuantifiersDown( alpha ) )

    case Quant( variable, alpha, pol ) => Quant( variable, moveUniversalQuantifiersDown( alpha ), pol )
    case AndOr( alpha, beta, connective ) => connective( moveUniversalQuantifiersDown( alpha ), moveUniversalQuantifiersDown( beta ) )

    case _ => formula
  }

  private def moveExistentialQuantifiersUp( formula: Formula ): Formula = formula match {
    case Or( Ex( variableAlpha, alpha ), Ex( variableBeta, beta ) ) => withNewVariable( variableAlpha, alpha, beta, { ( v, a, b ) => Ex( v, moveExistentialQuantifiersUp( Or( a, b ) ) ) } )
    case AndOr( alpha, Ex( variable, beta ), connective )           => withNewVariable( variable, alpha, beta, { ( v, a, b ) => Ex( v, moveExistentialQuantifiersUp( connective( a, b ) ) ) } )
    case AndOr( Ex( variable, beta ), alpha, connective )           => withNewVariable( variable, beta, alpha, { ( v, b, a ) => Ex( v, moveExistentialQuantifiersUp( connective( b, a ) ) ) } )

    case Quant( variable, alpha, pol )                              => Quant( variable, moveExistentialQuantifiersUp( alpha ), pol )
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

  def distributeConjunctionsOverDisjunctions( formula: Formula ): Formula = formula match {
    case Ex( variable, alpha )           => Ex( variable, distributeConjunctionsOverDisjunctions( alpha ) )
    case And( alpha, Or( beta, gamma ) ) => Or( ( And( alpha, beta ) ), ( And( alpha, gamma ) ) )
    case And( Or( alpha, beta ), gamma ) => Or( ( And( alpha, gamma ) ), ( And( beta, gamma ) ) )
    case And( alpha, beta ) => {
      val distributedAlpha = distributeConjunctionsOverDisjunctions( alpha )
      val distributedBeta = distributeConjunctionsOverDisjunctions( beta )
      if ( distributedAlpha != alpha || distributedBeta != beta )
        distributeConjunctionsOverDisjunctions( And( distributedAlpha, distributedBeta ) )
      else
        formula
    }
    case _ => formula
  }

  def moveQuantifiers: Formula => Formula =
    moveUniversalQuantifiersDown _ andThen
      moveExistentialQuantifiersUp _

  def disjunctions( formula: Formula ): Set[Formula] = formula match {
    case Or.nAry( disjunctions ) => disjunctions.toSet
    case _                       => Set( formula )
  }

  private object ExPrefix {
    def apply( existentialVariables: List[Var], formula: Formula ): Formula = existentialVariables match {
      case Nil              => formula
      case variable :: rest => Ex( variable, apply( rest, formula ) )
    }

    def unapply( formula: Formula ): Option[( List[Var], Formula )] = formula match {
      case Ex( variable, formula ) => {
        val ( variables, innerFormula ) = unapply( formula ).getOrElse( ( Nil, formula ) )
        Some( ( variable :: variables, innerFormula ) )
      }
      case _ => Some( Nil, formula )
    }
  }

  def polaritiesWithRespectTo( formula: Formula, variable: Var, polarity: Polarity = Polarity.Positive ): Set[Polarity] = formula match {
    case Atom( atomVariable, _ ) if atomVariable == variable => Set( polarity )
    case Neg( alpha ) => polaritiesWithRespectTo( alpha, variable, !polarity )
    case AndOr( alpha, beta, _ ) => polaritiesWithRespectTo( alpha, variable, polarity ) ++ polaritiesWithRespectTo( beta, variable, polarity )
    case Quant( _, alpha, _ ) => polaritiesWithRespectTo( alpha, variable, polarity )
    case _ => Set()
  }

  def polarityWithRespectTo( formula: Formula, variable: Var ): Option[Polarity] = {
    val polarities = polaritiesWithRespectTo( formula, variable )
    if ( polarities.size <= 1 )
      Some( polarities.headOption.getOrElse( Polarity.Positive ) )
    else
      None
  }

  def splitConjunctionWithRespectTo( formula: Formula, variable: Var ): Option[( List[Formula], List[Formula] )] = formula match {
    case And.nAry( conjuncts ) => {
      val conjunctsWithPolarities = conjuncts.map( conjunct => ( conjunct, polarityWithRespectTo( conjunct, variable ) ) )

      if ( conjunctsWithPolarities.exists( { case ( _, polarity ) => polarity == None } ) )
        None
      else {
        val positiveConjuncts = conjunctsWithPolarities.filter( _._2.get.positive ).map( _._1 )
        val negativeConjuncts = conjunctsWithPolarities.filter( _._2.get.negative ).map( _._1 )
        Some( ( positiveConjuncts, negativeConjuncts ) )
      }
    }
  }

  def preprocess( formula: Formula, variable: Var ): Option[Set[( List[Formula], List[Formula] )]] = {
    val nnf = toNNF( formula )

    val movedQuantifiers = moveQuantifiers( nnf )
    movedQuantifiers match {
      case ExPrefix( variables, innerFormula ) => {
        val distributedDisjunctions = distributeConjunctionsOverDisjunctions( innerFormula )

        val splits = disjunctions( distributedDisjunctions ).map( splitConjunctionWithRespectTo( _, variable ) )
        if ( splits.exists( _.isEmpty ) )
          None
        else
          Some( splits.map( _.get ) )
      }
    }
  }

  def apply( formula: Formula ): Option[Substitution] = formula match {
    case Ex( quantifierVariable, innerFormula ) => {
      // todo: allow multiple argument relations

      val splitDisjunctions = preprocess( formula, quantifierVariable )
      splitDisjunctions.map( disjunctions => {
        val witness = completeWitness( disjunctions, quantifierVariable )
        Substitution( Map( quantifierVariable -> Abs( FOLVar( "x" ), witness ) ) )
      } )
    }
    case _ => throw new Exception( "formula does not start with existential quantifier" )
  }
}
