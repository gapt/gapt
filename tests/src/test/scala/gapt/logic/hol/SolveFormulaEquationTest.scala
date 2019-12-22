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
import gapt.provers.escargot.Escargot
import org.specs2.matcher.Matcher
import gapt.expr.subst.Substitution
import gapt.expr.formula.hol.instantiate
import org.specs2.specification.core.Fragment

class SolveFormulaEquationTest extends Specification {

  private def beAnEquivalentSubstitutionFor( formula: Formula, equivalentSubstitution: Substitution ): Matcher[Substitution] = { substitution: Substitution =>
    val firstOrderPart = solveFormulaEquation.extractFirstOrderPart( formula )
    val substitutedFormula = BetaReduction.betaNormalize( substitution( firstOrderPart ) )
    val equivalentSubstitutedFormula = BetaReduction.betaNormalize( equivalentSubstitution( firstOrderPart ) )
    val isValid = Escargot isValid Iff( substitutedFormula, equivalentSubstitutedFormula )
    ( isValid, s"applying $substitution is not equivalent to applying $equivalentSubstitution to $formula" )
  }

  private def succeedFor( formulaEquation: Formula, expectedEquivalentSubstitution: Substitution ): Fragment = {
    s"succeed for $formulaEquation" >> {
      solveFormulaEquation( formulaEquation ) must
        beSome( beAnEquivalentSubstitutionFor( formulaEquation, expectedEquivalentSubstitution ) )
    }
  }

  "solveFormulaEquation" should {
    val X = Var( "X", Ti ->: To )
    succeedFor( hof"?X X(a)", Substitution( X, le"^x x=a" ) )
    succeedFor( hof"?X ((X(a) & -X(f(b))) | (X(f(b)) & -X(a)))", Substitution( X, le"^x (-f(b)=a -> x=a) & ((-(-f(b)=a)) & -a=f(b) -> x=f(b))" ) )
    succeedFor( hof"?X (X(a) & X(b))", Substitution( X, le"^x x=a | x=b" ) )
    succeedFor( hof"?X (X(a) | X(b))", Substitution( X, le"^x x=a" ) )
    succeedFor( hof"?X (-X(a) -> X(b))", Substitution( X, le"^x x=a" ) )
  }
}
