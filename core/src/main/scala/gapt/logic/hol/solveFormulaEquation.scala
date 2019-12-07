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

object solveFormulaEquation {
  def apply( formula: Formula ): Try[Formula] = Try( formula match {
    case Ex( quantifierVariable, innerFormula ) => {
      // todo: allow multiple argument relations
      require( quantifierVariable.ty == Ti ->: To, "first existential quantifier variable must be of a relation type" )
      require( !containsHOQuantifier( innerFormula ), "inner formula must be first order" )

      require( !containsQuantifier( innerFormula ), "inner formula must be quantifier-free" )

      val dnf = DNFp( innerFormula )

      val witnessClauses = for {
        clause <- dnf
        positiveOccurrences = clause.succedent.filter(
          atom => atom match {
            case Atom( variable, _ ) => variable == quantifierVariable
            case _                   => false
          } )
        otherOccurrences = clause.antecedent.map( Neg.apply ) ++ clause.succedent.filterNot( positiveOccurrences.contains )
        witnessComponent = Or( positiveOccurrences.map(
          atom => atom match {
            // todo: handle multiple arguments
            // todo: unique name for unbound variable "x"
            case Atom( _, args ) => Eq( FOLVar( "x" ), args.head )
          } ) )
      } yield ( witnessComponent, otherOccurrences.map( occurrence => normalize( Substitution( Map( quantifierVariable -> Abs( FOLVar( "x" ), witnessComponent ) ) )( occurrence ) ) ) )

      val result = witnessClauses.tail.foldLeft( ( Imp( And( witnessClauses.head._2 ), witnessClauses.head._1 ), Vector( Neg( And( witnessClauses.head._2 ) ) ) ) )( ( current, next ) => {
        ( current, next ) match {
          case ( ( witness, implicationPrefix ), ( witnessComponent, otherOccurrences ) ) => {
            ( And( witness, Imp( And( implicationPrefix ++ otherOccurrences ), witnessComponent ) ), implicationPrefix :+ Neg( And( otherOccurrences ) ) )
          }
        }
      } )

      result._1
    }
    case _ => throw new Exception( "formula does not start with existential quantifier" )
  } )
}
