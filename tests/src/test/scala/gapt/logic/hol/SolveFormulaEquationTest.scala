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
import gapt.expr.subst.Substitution
import gapt.expr.formula.hol.instantiate
import org.specs2.specification.core.Fragment

class SolveFormulaEquationTest extends Specification {

  private def beAnEquivalentSubstitutionFor( formula: Formula, equivalentSubstitution: Substitution ): Matcher[Substitution] = { substitution: Substitution =>
    val firstOrderPart = solveFormulaEquation.extractFirstOrderPart( formula )
    val substitutedFormula = BetaReduction.betaNormalize( substitution( firstOrderPart ) )
    val equivalentSubstitutedFormula = BetaReduction.betaNormalize( equivalentSubstitution( firstOrderPart ) )
    val isValid = Sat4j isValid Iff( substitutedFormula, equivalentSubstitutedFormula )
    ( isValid, s"$substitution is not an equivalent substitution for $formula" )
  }

  private def succeedFor( formulaEquation: Formula, expectedEquivalentSubstitution: Substitution ): Fragment = {
    s"succeed for $formulaEquation" >> {
      solveFormulaEquation( formulaEquation ) must
        beAnEquivalentSubstitutionFor( formulaEquation, expectedEquivalentSubstitution )
    }
  }

  "solveFormulaEquation" should {
    succeedFor( hof"?X X(a)", Substitution( Map( Var( "X", Ti ->: To ) -> le"^x x=a" ) ) )
    succeedFor( hof"?X ((X(a) & -X(f(b))) | (X(f(b)) & -X(a)))", Substitution( Map( Var( "X", Ti ->: To ) -> le"^x (-f(b)=a -> x=a) & ((-(-f(b)=a)) & -a=f(b) -> x=f(b))" ) ) )
  }
}
