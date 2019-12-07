package gapt.logic.hol

import org.specs2.mutable._
import gapt.expr.Var
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.expr.formula._
import gapt.expr.formula.fol._
import _root_.gapt.expr.Const
import gapt.expr.formula.fol.FOLFunction
import gapt.expr._
import scala.util.Success
import gapt.provers.sat._
import org.specs2.matcher.Matcher

class SolveFormulaEquationTest extends Specification {

  private def beLogicallyEquivalentTo( thatFormula: Formula ): Matcher[Formula] =
    ( Sat4j isValid Iff( _: Formula, thatFormula ), s"is not logically equivalent to '$thatFormula'" )

  "solveFormulaEquation" should {
    "succeed for ?X X(a)" in {
      solveFormulaEquation( hof"?X X(a)" ) must
        beSuccessfulTry.withValue( beLogicallyEquivalentTo( fof"x=a" ) )
    }

    "succeed for ?X ((X(a) & -X(f(b))) | (X(f(b)) & -X(a)))" in {
      solveFormulaEquation( hof"?X ((X(a) & -X(f(b))) | (X(f(b)) & -X(a)))" ) must
        beSuccessfulTry.withValue( beLogicallyEquivalentTo( fof"(-f(b)=a -> x=a) & ((-(-f(b)=a)) & -a=f(b) -> x=f(b))" ) )
    }
  }
}