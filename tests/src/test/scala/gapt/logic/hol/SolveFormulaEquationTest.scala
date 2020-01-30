package gapt.logic.hol

import gapt.expr._
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.{ And, Formula, Iff }
import gapt.expr.subst.Substitution
import gapt.proofs.HOLSequent
import gapt.provers.escargot.Escargot
import org.specs2.matcher.Matcher
import org.specs2.mutable.Specification
import org.specs2.specification.core.Fragment

import scala.util.Try

class SolveFormulaEquationTest extends Specification {

  "preprocess" should {
    def succeedWithSequents(
      formulaEquation:  ( Var, Formula ),
      expectedSequents: Set[HOLSequent] ): Fragment = {
      succeedWithExPrefixAndSequents( formulaEquation, ( Nil, expectedSequents ) )
    }

    def succeedWithExPrefixAndSequents(
      formulaEquation: ( Var, Formula ),
      expectedResult:  ( List[FOLVar], Set[HOLSequent] ) ): Fragment = {
      val ( secondOrderVariable, formula ) = formulaEquation
      val ( existentialVariables, expectedSequents ) = expectedResult
      s"succeed for $formula" >> {
        Try( solveFormulaEquation.preprocess( secondOrderVariable, formula ) ) must beSuccessfulTry(
          { result: ( List[FOLVar], Set[HOLSequent] ) =>
            val ( variables, disjuncts ) = result
            val substitution = Substitution( existentialVariables.zip( variables ).toMap )
            val substitutedSequents = expectedSequents
              .map( sequent => sequent.map( f => substitution( f ) ) )
            val multiSetEquals = ( s1: HOLSequent, s2: HOLSequent ) => s1.multiSetEquals( s2 )
            disjuncts must beSetEqualsWithCustomEquality(
              substitutedSequents,
              multiSetEquals )
          } )
      }
    }

    def formulaEquation( variable: Var, formula: Formula ) = ( variable, formula )

    def formulaEquationInX( formula: Formula ) = formulaEquation( hov"X:i>o", formula )

    val fe = formulaEquationInX _ // alias to shorten test cases
    succeedWithSequents( fe( hof"R(a)" ), Set( hos"⊢ R(a)" ) )
    succeedWithSequents( fe( hof"X(a)" ), Set( hos"⊢ X(a)" ) )
    succeedWithSequents( fe( hof"¬X(a)" ), Set( hos"¬X(a) ⊢" ) )
    succeedWithSequents( fe( hof"X(b) ∧ ¬X(a)" ), Set( hos"¬X(a) ⊢ X(b)" ) )
    succeedWithSequents(
      fe( hof"R(a) ∧ X(b) ∧ ¬X(a)" ),
      Set( hos"¬X(a) ⊢ R(a), X(b)" ) )
    succeedWithSequents(
      fe( hof"X(a) ∨ X(b)" ),
      Set( hos"⊢ X(a)", hos"⊢ X(b)" ) )
    succeedWithSequents(
      fe( hof"X(a) ∧ (¬X(b) ∨ X(c))" ),
      Set( hos"¬X(b) ⊢ X(a)", hos"⊢ X(c), X(a)" ) )
    succeedWithSequents(
      fe( hof"X(a) ∧ (¬X(b) ∨ X(c)) ∧ ¬X(d)" ),
      Set( hos"¬X(b), ¬X(d) ⊢ X(a)", hos"¬X(d) ⊢ X(c), X(a)" ) )
    succeedWithSequents(
      fe( hof"Y(a) ∧ (¬Y(b) ∨ Y(c)) ∧ ¬Y(d)" ),
      Set( hos"⊢ Y(a), ¬Y(b), ¬Y(d)", hos"⊢ Y(a), Y(c), ¬Y(d)" ) )
    succeedWithSequents(
      fe( hof"∀x (X(x) ∧ X(a))" ),
      Set( hos"⊢ ∀x X(x), ∀x X(a)" ) )
    succeedWithExPrefixAndSequents(
      fe( hof"∃x X(x)" ),
      ( List( FOLVar( "x" ) ), Set( hos"⊢ X(x)" ) ) )
    succeedWithSequents(
      fe( hof"∀x ∃y X(x,y)" ),
      Set( hos"⊢ ∀x ∃y X(x,y)" ) )
    succeedWithExPrefixAndSequents(
      fe( hof"(∃y X(a,y)) ∨ (∃x X(b,x))" ),
      ( List( FOLVar( "z" ) ), Set( hos"⊢ X(a, z)", hos"⊢ X(b, z)" ) ) )
    succeedWithSequents(
      fe( hof"(∀x (X(x) -> (∀y R(x,y)))) ∧ (X(a) ∨ X(b))" ),
      Set( hos"∀x (¬X(x) ∨ (∀y R(x, y))) ⊢ X(a)", hos"∀x (¬X(x) ∨ (∀y R(x, y))) ⊢ X(b)" ) )
  }

  "findPartialWitness" should {
    def succeedFor(
      secondOrderVariable: Var,
      sequent:             HOLSequent,
      expectedWitness:     Expr ): Fragment = {
      s"succeed for $sequent" >> {
        val argumentVariables = expectedWitness match {
          case Abs.Block( variables, _ ) => variables.asInstanceOf[List[FOLVar]]
        }
        val witness = solveFormulaEquation.findPartialWitness(
          secondOrderVariable,
          argumentVariables,
          sequent )
        val formula = And( sequent.antecedent ++ sequent.succedent )
        val expectedSubstitution = Substitution( secondOrderVariable -> expectedWitness )
        val substitution = Substitution( secondOrderVariable -> Abs( argumentVariables, witness ) )
        ( substitution, formula ) must beAnEquivalentSubstitutionTo( expectedSubstitution )
      }
    }

    succeedFor( hov"X:i>o", hos"R(a) ⊢", le"λt ⊤" )
    succeedFor( hov"X:i>o", hos"⊢ X(a)", le"λt t=a" )
    succeedFor( hov"X:i>o", hos"⊢ ∀x X(x)", le"λt ⊤" )
    succeedFor( hov"X:i>o", hos"⊢ ∀x (X(x) ∨ R(x))", le"λt ¬R(t)" )
    succeedFor( hov"X:i>o", hos"∀x (¬X(x) ∨ (∀y R(x, y))) ⊢ X(a)", le"λt t=a" )
    succeedFor( hov"X:i>o", hos"∀x (¬X(x) ∨ (∀y R(x, y))) ⊢ X(a)", le"λt ∀y R(t, y)" )
    succeedFor( hov"X:i>o", hos"¬X(a) ⊢ ∀x (X(x) ∨ (∀y R(x, y)))", le"λt t!=a" )
    succeedFor( hov"X:i>o", hos"⊢ ∀x X(x)", le"λt ⊤" )
  }

  "solveFormulaEquation" should {
    def succeedFor(
      formulaEquation:                Formula,
      expectedEquivalentSubstitution: Substitution ): Fragment = {
      s"succeed for $formulaEquation" in {
        solveFormulaEquation( formulaEquation ) must
          beSuccessfulTry( beAnEquivalentSubstitutionTo( expectedEquivalentSubstitution ) )
      }
    }

    def failFor( formulaEquation: Formula ): Fragment = {
      s"fail for $formulaEquation" in {
        solveFormulaEquation( formulaEquation ) must beFailedTry
      }
    }

    val X = hov"X:i>o"
    succeedFor( hof"∃(X: i>o) R(a)", Substitution( X -> le"λx ⊤" ) )
    succeedFor( hof"∃X X(a)", Substitution( X -> le"λx x=a" ) )
    succeedFor( hof"∃X (X(a) ∧ ¬X(b))", Substitution( X -> le"λx x=a" ) )
    succeedFor( hof"∃X (X(c) -> P(c))", Substitution( X -> le"λt t!=c" ) )
    succeedFor( hof"∃X (¬X(c) ∧ P(c))", Substitution( X -> le"λt ⊥" ) )
    succeedFor(
      hof"∃X ((X(a) ∧ ¬X(f(b))) ∨ (X(f(b)) ∧ ¬X(a)))",
      Substitution( X -> le"λx (¬f(b)=a -> x=a) ∧ ((¬(¬f(b)=a)) ∧ ¬a=f(b) -> x=f(b))" ) )
    succeedFor( hof"∃X (X(a) ∧ X(b))", Substitution( X -> le"λx x=a ∨ x=b" ) )
    succeedFor( hof"∃X (X(a) ∨ X(b))", Substitution( X -> le"λx x=a" ) )
    succeedFor( hof"∃X (¬X(a) -> X(b))", Substitution( X -> le"λx x=a" ) )
    succeedFor( hof"∃(X: i>o) (R(a) ∧ X(b))", Substitution( X -> le"λx x=b" ) )
    succeedFor(
      hof"∃X (∃Y (X(a) ∧ Y(b)))",
      Substitution( hov"X:i>o" -> le"λx x=a", hov"Y:i>o" -> le"λx x=b" ) )
    succeedFor(
      hof"∃X X(a,b)",
      Substitution( hov"X:i>i>o" -> le"λx_1 (λx_2 x_1 = a ∧ x_2 = b)" ) )
    succeedFor( hof"∃X ((∀x (X(x) -> R(x))) ∧ X(a))", Substitution( X -> le"λt R(t):o" ) )
    succeedFor(
      hof"∃X ((∀x (X(x) -> (∀y R(x, y)))) ∧ X(a))",
      Substitution( X -> le"λt ∀y R(t, y)" ) )
    succeedFor(
      hof"∃X ((∀x (X(x) -> R(x))) ∧ (X(a) ∨ X(b)))",
      Substitution( X -> le"λt (R:i>o)(t)" ) )
    succeedFor(
      hof"∃X ((∀x (X(x) -> (∀y R(x, y)))) ∧ (X(a) ∨ X(b)))",
      Substitution( X -> le"λt ∀y R(t, y)" ) )
    succeedFor(
      hof"∃X (∀x ((∀y R(x,y)) -> X(x)) ∧ (¬X(a) ∨ ¬X(b)))",
      Substitution( X -> le"λt ∀y R(t,y)" ) )
    succeedFor(
      hof"∃X (∀x ∀y (R(x,y) -> X(x)) ∧ (¬X(a) ∨ ¬X(b)))",
      Substitution( X -> le"λt ∃y R(t,y)" ) )
    succeedFor(
      hof"∃X (∀x ∀y (X(x, y) -> R(x, y)) ∧ (X(a, b) ∨ X(b, c)))",
      Substitution( hov"X:i>i>o" -> le"R:i>i>o" ) )
    succeedFor(
      hof"∃X (∀x ((∀y R(x,y)) -> X(x)) ∧ (X(a) ∨ ¬X(b)) ∧ ¬X(c))",
      Substitution( X -> le"λt ((¬(c=a ∨ ∀y R(c, y))) -> (t=a ∨ ∀y R(t,y))) ∧ (((c=a ∨ ∀y R(c, y)) ∧ ¬(∀y R(b, y)) ∧ ¬(∀y R(c, y))) -> ∀y R(t, y))" ) )
    succeedFor(
      hof"∃X (∀x (X(x) ∨ R(x)))",
      Substitution( hov"X:i>o" -> le"λx ∃t x=t" ) )
    succeedFor(
      hof"∃X (X(a) ∧ ∃x X(x))",
      Substitution( X -> le"λt t=a" ) )
    succeedFor(
      hof"∃X ((∃x X(x)) ∧ ¬R(a))",
      Substitution( X -> le"λt ⊤" ) )
    succeedFor(
      hof"∃X ∃x X(x,a)",
      Substitution( hov"X:i>i>o" -> le"λt λs s=a" ) )
    succeedFor(
      hof"∃X ((R(a) ∧ ∃x X(x)) ∨ ((∃y R(y)) ∨ X(b)))",
      Substitution( X -> le"λt t=b" ) )
    succeedFor(
      hof"∃X ∀x (R(a) ∨ X(x) ∨ R(b))",
      Substitution( X -> le"λt ¬R(a) ∧ ¬R(b)" ) )
    succeedFor(
      hof"∃X (∀x ∃y X(x))",
      Substitution( X -> le"λt ∃x x=t" ) )
    succeedFor(
      hof"∃X (∀x (P(x) -> X(x)))",
      Substitution( X -> le"P:i>o" ) )
    succeedFor( hof"∃X (¬X(a, b) ∧ ∀x ∃y X(x, y))", Substitution( hov"X:i>i>o" -> le"λt_1 λt_2 (t_1 != a ∨ t_2 != b)" ) )
    succeedFor( hof"∃X ∀x ∃y X(x,y)", Substitution( hov"X:i>i>o" -> le"λt_1 λt_2 ⊤" ) )
    succeedFor( hof"∃X ∀x (X(x) ∧ R(x))", Substitution( X -> le"λt ∃x x=t" ) )
    succeedFor( hof"∃X ∀x (X(f(x)) ∨ R(x))", Substitution( X -> le"λt ∃x (t=f(x) ∧ ¬R(x))" ) )
    failFor( hof"∃X ∀x (X(x,a) ∨ ∀y ¬X(x, y))" )
    failFor( hof"∃X ((∀x ∃y X(x, y)) ∧ (∀x ∃y ¬X(y, x)))" )
  }

  private def beSetEqualsWithCustomEquality[A](
    expectedSet: Set[A],
    equals:      ( A, A ) => Boolean ): Matcher[Set[A]] = ( thisSet: Set[A] ) => {
    val inExpectedAndNotInThis = expectedSet.filterNot( x => thisSet.exists( equals( x, _ ) ) )
    val inThisAndNotInExpected = thisSet.filterNot( x => expectedSet.exists( equals( x, _ ) ) )
    val errorMessage =
      s"""
         |$thisSet is not equal to $expectedSet according to the given equality
         |Expected, but not present:
         |${inExpectedAndNotInThis.mkString( "\n" )}
         |
         |Unexpected, but present:
         |${inThisAndNotInExpected.mkString( "\n" )}
    """.stripMargin
    val areEqual = inExpectedAndNotInThis.isEmpty && inThisAndNotInExpected.isEmpty
    ( areEqual, errorMessage )
  }

  private def beAnEquivalentSubstitutionTo(
    equivalentSubstitution: Substitution ): Matcher[( Substitution, Formula )] = {
    input: ( Substitution, Formula ) =>
      {
        val ( substitution, firstOrderPart ) = input
        val substitutedFormula = simplify( BetaReduction.betaNormalize(
          substitution( firstOrderPart ) ) )
        val equivalentSubstitutedFormula = simplify( BetaReduction.betaNormalize(
          equivalentSubstitution( firstOrderPart ) ) )
        val isValid = Escargot isValid Iff( substitutedFormula, equivalentSubstitutedFormula )
        val errorMessage =
          s"""|applying $substitution is not equivalent to applying $equivalentSubstitution to $firstOrderPart
            |applying $substitution
            |gives $substitutedFormula
            |applying $equivalentSubstitution
            |gives $equivalentSubstitutedFormula
          """.stripMargin
        ( isValid, errorMessage )
      }
  }
}
