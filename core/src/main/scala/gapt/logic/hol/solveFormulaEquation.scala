package gapt.logic.hol
import gapt.expr.formula._
import gapt.expr.formula.fol._
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

/**
 * Uses the DLS algorithm to find a witness for formula equations
 * of the form ?X φ where φ is a first order formula
 *
 * At the moment φ may only be a quantifier free formula
 * and the quantified relation must be unary
 */
object solveFormulaEquation {

  private def relationOccurrences( clause: HOLClause, quantifierVariable: Var ): ( Vector[Formula], Vector[Formula] ) = {
    val positiveOccurrences = clause.succedent.filter(
      atom => atom match {
        case Atom( variable, _ ) => variable == quantifierVariable
        case _                   => false
      } )
    val nonPositiveOcurrences = clause.antecedent.map( Neg.apply ) ++
      clause.succedent.filterNot( positiveOccurrences.contains )

    ( positiveOccurrences, nonPositiveOcurrences )
  }

  private def partialWitness( positiveOccurrences: Vector[Formula] ): Formula = {
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

  private def completeWitness( dnf: Set[HOLClause], quantifierVariable: Var ): Formula = {
    val witnessClauses = for {
      clause <- dnf
      ( positiveOccurrences, nonPositiveOcurrences ) = relationOccurrences( clause, quantifierVariable )
      witnessPart = partialWitness( positiveOccurrences )
    } yield ( witnessPart, And( nonPositiveOcurrences.map( substituteWitness( _, quantifierVariable, witnessPart ) ) ) )

    val witnessConjuncts = witnessClauses.toList.inits.toTraversable.init.map( initList => {
      val witnessPart = initList.last._1
      val nonPositiveOcurrence = initList.last._2
      Imp( And( initList.init.map( element => Neg( element._2 ) ) :+ nonPositiveOcurrence ), witnessPart )
    } )

    And( witnessConjuncts )
  }

  def apply( formula: Formula ): Try[Formula] = Try( formula match {
    case Ex( quantifierVariable, innerFormula ) => {
      // todo: allow multiple argument relations

      val dnf = DNFp( innerFormula )
      completeWitness( dnf, quantifierVariable )
    }
    case _ => throw new Exception( "formula does not start with existential quantifier" )
  } )
}
