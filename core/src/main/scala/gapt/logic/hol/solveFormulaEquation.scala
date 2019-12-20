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
      val ( witnessPart, nonPositiveOcurrence ) = initList.last
      Imp( And( initList.init.map( element => Neg( element._2 ) ) :+ nonPositiveOcurrence ), witnessPart )
    } )

    And( witnessConjuncts )
  }

  def apply( formula: Formula ): Substitution = formula match {
    case Ex( quantifierVariable, innerFormula ) => {
      // todo: allow multiple argument relations

      val dnf = DNFp( innerFormula )
      val witness = completeWitness( dnf, quantifierVariable )
      Substitution( Map( quantifierVariable -> Abs( FOLVar( "x" ), witness ) ) )
    }
    case _ => throw new Exception( "formula does not start with existential quantifier" )
  }
}
