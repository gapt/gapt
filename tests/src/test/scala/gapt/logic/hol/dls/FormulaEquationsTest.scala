package gapt.logic.hol.dls

import gapt.expr._
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.And
import gapt.expr.formula.Formula
import gapt.expr.formula.Iff
import gapt.expr.subst.Substitution
import gapt.expr.ty.FunctionType
import gapt.logic.hol.simplifyPropositional
import gapt.logic.hol.solveFormulaEquation
import gapt.proofs.HOLSequent
import gapt.provers.escargot.Escargot
import gapt.utils.NameGenerator
import org.specs2.matcher.Matcher
import org.specs2.mutable.Specification
import org.specs2.specification.core.Fragment

import scala.util.Try

class FormulaEquationsTest extends Specification {

  private def toDisjunct(s: HOLSequent): Disjunct =
    Disjunct(s.antecedent, s.succedent)

  "preprocess" should {
    def succeedWithSequents(
        formulaEquation: (Var, Formula),
        expectedSequents: Set[HOLSequent]
    ): Fragment = {
      succeedWithExPrefixAndSequents(formulaEquation, expectedSequents)
    }

    def succeedWithExPrefixAndSequents(
        formulaEquation: (Var, Formula),
        expectedResult: Set[HOLSequent]
    ): Fragment = {
      val (secondOrderVariable, formula) = formulaEquation
      s"succeed for $formula" >> {
        Try(new DlsPreprocessor(secondOrderVariable).preprocess(formula)) must beSuccessfulTry({ (result: Set[Disjunct]) =>
          val multiSetEquals = (s1: Disjunct, s2: Disjunct) => s1.multiSetEquals(s2)
          result must beSetEqualsWithCustomEquality(
            expectedResult.map(toDisjunct),
            multiSetEquals
          )
        })
      }
    }

    def formulaEquation(variable: Var, formula: Formula) = (variable, formula)

    def formulaEquationInX(formula: Formula) = formulaEquation(hov"X:i>o", formula)

    val fe = formulaEquationInX _ // alias to shorten test cases
    succeedWithSequents(fe(hof"R(a)"), Set())
    succeedWithSequents(fe(hof"X(a)"), Set(hos"⊢ X(a)"))
    succeedWithSequents(fe(hof"¬X(a)"), Set(hos"¬X(a) ⊢"))
    succeedWithSequents(fe(hof"X(b) ∧ ¬X(a)"), Set(hos"¬X(a) ⊢ X(b)"))
    succeedWithSequents(
      fe(hof"R(a) ∧ X(b) ∧ ¬X(a)"),
      Set(hos"¬X(a) ⊢ R(a), X(b)")
    )
    succeedWithSequents(
      fe(hof"X(a) ∨ X(b)"),
      Set(hos"⊢ X(a)", hos"⊢ X(b)")
    )
    succeedWithSequents(
      fe(hof"X(a) ∧ (¬X(b) ∨ X(c))"),
      Set(hos"¬X(b) ⊢ X(a)", hos"⊢ X(c), X(a)")
    )
    succeedWithSequents(
      fe(hof"X(a) ∧ (¬X(b) ∨ X(c)) ∧ ¬X(d)"),
      Set(hos"¬X(b), ¬X(d) ⊢ X(a)", hos"¬X(d) ⊢ X(c), X(a)")
    )
    succeedWithSequents(
      fe(hof"Y(a) ∧ (¬Y(b) ∨ Y(c)) ∧ ¬Y(d)"),
      Set()
    )
    succeedWithSequents(
      fe(hof"∀x (X(x) ∧ X(a))"),
      Set(hos"⊢ ∀x X(x), ∀x X(a)")
    )
    succeedWithSequents(
      fe(hof"∃x X(x)"),
      Set(hos"⊢ ∃x X(x)")
    )
    succeedWithSequents(
      formulaEquation(hov"X:i>i>o", hof"∀x ∃y X(x,y)"),
      Set(hos"⊢ ∀x ∃y X(x,y)")
    )
    succeedWithSequents(
      fe(hof"(∀x (X(x) -> (∀y R(x,y)))) ∧ (X(a) ∨ X(b))"),
      Set(hos"∀x (¬X(x) ∨ (∀y R(x, y))) ⊢ X(a)", hos"∀x (¬X(x) ∨ (∀y R(x, y))) ⊢ X(b)")
    )
  }

  "findPartialWitness" should {

    def succeedFor(
        secondOrderVariable: Var,
        sequent: HOLSequent,
        expectedWitness: Expr
    ): Fragment = {
      s"succeed for $sequent" >> {
        val argumentVariables = expectedWitness match {
          case Abs.Block(variables, _) => variables.asInstanceOf[List[FOLVar]]
        }
        val witness =
          new DlsPartialWitnessExtraction(secondOrderVariable)
            .findPartialWitness(argumentVariables, toDisjunct(sequent))
        val formula = And(sequent.antecedent ++ sequent.succedent)
        val expectedSubstitution = Substitution(secondOrderVariable -> expectedWitness)
        val substitution = Substitution(secondOrderVariable -> Abs(argumentVariables, witness))
        (substitution, formula) must beAnEquivalentSubstitutionTo(expectedSubstitution)
      }
    }

    def failFor(
        secondOrderVariable: Var,
        sequent: HOLSequent
    ): Fragment = {
      s"fail for $sequent" >> {
        val FunctionType(_, argumentTypes) = secondOrderVariable.ty: @unchecked
        val argumentVariables = new NameGenerator(Nil).freshStream(secondOrderVariable.name).take(argumentTypes.length).map(FOLVar(_)).toList
        new DlsPartialWitnessExtraction(secondOrderVariable)
          .findPartialWitness(argumentVariables, toDisjunct(sequent)) must throwA[Exception]
      }
    }

    succeedFor(hov"X:i>o", hos"R(a) ⊢", le"λt ⊤")
    succeedFor(hov"X:i>o", hos"⊢ X(a)", le"λt t=a")
    succeedFor(hov"X:i>o", hos"⊢ ∀x X(x)", le"λt ⊤")
    succeedFor(hov"X:i>o", hos"⊢ ∀x (X(x) ∨ R(x))", le"λt ¬R(t)")
    succeedFor(hov"X:i>o", hos"∀x (¬X(x) ∨ (∀y R(x, y))) ⊢ X(a)", le"λt t=a")
    succeedFor(hov"X:i>o", hos"∀x (¬X(x) ∨ (∀y R(x, y))) ⊢ X(a)", le"λt ∀y R(t, y)")
    succeedFor(hov"X:i>o", hos"¬X(a) ⊢ ∀x (X(x) ∨ (∀y R(x, y)))", le"λt t!=a")
    succeedFor(hov"X:i>o", hos"⊢ ∀x X(x)", le"λt ⊤")
    succeedFor(hov"X:i>o", hos"(∀x (¬X(x) ∨ S(x))) ⊢ (∀x (¬R(x) ∨ X(x)))", le"λt R(t):o")
    succeedFor(hov"X:i>o", hos"¬X(c) ∨ P(c) ⊢", le"λt t != c")
    failFor(hov"X:i>o", hos"¬X(c) ∨ ¬X(d) ⊢ X(a) ∨ X(b)")
  }

  "simplify" should {
    def succeedFor(inputFormula: Formula, expectedSimplifiedFormula: Formula): Fragment = {
      s"""map "$inputFormula" to "$expectedSimplifiedFormula"""" in {
        simplify(inputFormula) must beEqualTo(expectedSimplifiedFormula)
      }
    }

    succeedFor(hof"(P ∨ Q) ∧ P", hof"P")
    succeedFor(hof"c=c", hof"⊤")
    succeedFor(hof"c!=c", hof"⊥")
    succeedFor(hof"P ∧ P ∧ P", hof"P")
    succeedFor(hof"!x (x=t -> P(x))", hof"P(t)")
    succeedFor(hof"!x (P(x) ∨ x!=t)", hof"P(t)")
    succeedFor(hof"P -> ¬P", hof"¬P")
    succeedFor(hof"¬(¬P)", hof"P")
    succeedFor(hof"P ∨ Q ∨ P", hof"P ∨ Q")
    succeedFor(hof"(P ∧ Q ∧ R) ∨ P", hof"P")
    succeedFor(hof"(P ∨ Q ∨ R) ∧ P", hof"P")
    succeedFor(hof"P ∧ ⊤", hof"P")
    succeedFor(hof"P ∧ ⊥", hof"⊥")
    succeedFor(hof"⊥ ∨ P", hof"P")
    succeedFor(hof"⊤ ∨ P", hof"⊤")
    succeedFor(hof"P ∧ ¬P ∧ Q", hof"⊥")
    succeedFor(hof"P ∨ ¬P ∨ Q", hof"⊤")
    succeedFor(hof"a=b ∧ b=a", hof"a=b")
    succeedFor(hof"∀x (x=a ∧ x=b -> R(x))", hof"a!=b ∨ R(a)")
    succeedFor(hof"∃x x=a", hof"⊤")
    succeedFor(hof"∃x (x=a ∧ R(x))", hof"R(a)")
    succeedFor(hof"∀x ⊤", hof"⊤")
    succeedFor(hof"∃x ⊤", hof"⊤")
    succeedFor(hof"∀x ⊥", hof"⊥")
    succeedFor(hof"∃x ⊥", hof"⊥")
    succeedFor(hof"∀x (R(a))", hof"R(a)")
    succeedFor(hof"P -> P", hof"⊤")
    succeedFor(hof"(¬P ∨ Q) ∧ ¬P", hof"¬P")
    succeedFor(hof"(P -> Q) ∧ ¬P", hof"¬P")
    succeedFor(hof"P ∧ (Q ∨ (P ∧ Q))", hof"P ∧ Q")
    succeedFor(hof"P ∨ (Q ∨ (P ∧ Q))", hof"P ∨ Q")
    succeedFor(hof"a!=b ∧ b!=a", hof"a!=b")
  }

  "dls" should {
    def succeedFor(
        formulaEquation: Formula,
        expectedEquivalentSubstitution: Substitution
    ): Fragment = {
      s"succeed for $formulaEquation" in {
        dls(formulaEquation) must
          beSuccessfulTry(beAnEquivalentSubstitutionTo(expectedEquivalentSubstitution))
      }
    }

    def extractCorrectly(formulaEquation: Formula, expectedInnerFormula: Formula): Fragment = {
      s"extract $expectedInnerFormula from $formulaEquation" in {
        dls(formulaEquation) must beSuccessfulTry((_: (Substitution, Formula)) must beLike {
          case (_, innerFormula: Formula) => innerFormula must beEqualTo(expectedInnerFormula)
        })
      }
    }

    def failFor(formulaEquation: Formula): Fragment = {
      s"fail for $formulaEquation" in {
        dls(formulaEquation) must beFailedTry
      }
    }

    val X = hov"X:i>o"
    succeedFor(hof"∃(X: i>o) R(a)", Substitution(X -> le"λx ⊤"))
    succeedFor(hof"∃X X(a)", Substitution(X -> le"λx x=a"))
    succeedFor(hof"∃X (X(a) ∧ ¬X(b))", Substitution(X -> le"λx x=a"))
    succeedFor(hof"∃X (X(c) -> P(c))", Substitution(X -> le"λt t!=c"))
    succeedFor(hof"∃X (¬X(c) ∧ P(c))", Substitution(X -> le"λt ⊥"))
    succeedFor(
      hof"∃X ((X(a) ∧ ¬X(f(b))) ∨ (X(f(b)) ∧ ¬X(a)))",
      Substitution(X -> le"λx (¬f(b)=a -> x=a) ∧ ((¬(¬f(b)=a)) ∧ ¬a=f(b) -> x=f(b))")
    )
    succeedFor(hof"∃X (X(a) ∧ X(b))", Substitution(X -> le"λx x=a ∨ x=b"))
    succeedFor(hof"∃X (X(a) ∨ X(b))", Substitution(X -> le"λx x=a"))
    succeedFor(hof"∃X (¬X(a) -> X(b))", Substitution(X -> le"λx x=a"))
    succeedFor(hof"∃(X: i>o) (R(a) ∧ X(b))", Substitution(X -> le"λx x=b"))
    succeedFor(
      hof"∃X (∃Y (X(a) ∧ Y(b)))",
      Substitution(hov"X:i>o" -> le"λx x=a", hov"Y:i>o" -> le"λx x=b")
    )
    succeedFor(
      hof"∃X X(a,b)",
      Substitution(hov"X:i>i>o" -> le"λx_1 (λx_2 x_1 = a ∧ x_2 = b)")
    )
    succeedFor(hof"∃X ((∀x (X(x) -> R(x))) ∧ X(a))", Substitution(X -> le"λt R(t):o"))
    succeedFor(
      hof"∃X ((∀x (X(x) -> (∀y R(x, y)))) ∧ X(a))",
      Substitution(X -> le"λt ∀y R(t, y)")
    )
    succeedFor(
      hof"∃X ((∀x (X(x) -> R(x))) ∧ (X(a) ∨ X(b)))",
      Substitution(X -> le"λt (R:i>o)(t)")
    )
    succeedFor(
      hof"∃X ((∀x (X(x) -> (∀y R(x, y)))) ∧ (X(a) ∨ X(b)))",
      Substitution(X -> le"λt ∀y R(t, y)")
    )
    succeedFor(
      hof"∃X (∀x ((∀y R(x,y)) -> X(x)) ∧ (¬X(a) ∨ ¬X(b)))",
      Substitution(X -> le"λt ∀y R(t,y)")
    )
    succeedFor(
      hof"∃X (∀x ∀y (R(x,y) -> X(x)) ∧ (¬X(a) ∨ ¬X(b)))",
      Substitution(X -> le"λt ∃y R(t,y)")
    )
    succeedFor(
      hof"∃X (∀x ∀y (X(x, y) -> R(x, y)) ∧ (X(a, b) ∨ X(b, c)))",
      Substitution(hov"X:i>i>o" -> le"R:i>i>o")
    )
    succeedFor(
      hof"∃X (∀x ((∀y R(x,y)) -> X(x)) ∧ (X(a) ∨ ¬X(b)) ∧ ¬X(c))",
      Substitution(X -> le"λt ((¬(c=a ∨ ∀y R(c, y))) -> (t=a ∨ ∀y R(t,y))) ∧ (((c=a ∨ ∀y R(c, y)) ∧ ¬(∀y R(b, y)) ∧ ¬(∀y R(c, y))) -> ∀y R(t, y))")
    )
    succeedFor(
      hof"∃X (∀x (X(x) ∨ R(x)))",
      Substitution(hov"X:i>o" -> le"λx ∃t x=t")
    )
    succeedFor(
      hof"∃X (X(a) ∧ ∃x X(x))",
      Substitution(X -> le"λt ⊤")
    )
    succeedFor(
      hof"∃X ((∃x X(x)) ∧ ¬R(a))",
      Substitution(X -> le"λt ⊤")
    )
    succeedFor(
      hof"∃X ∃x X(x,a)",
      Substitution(hov"X:i>i>o" -> le"λt λs ⊤")
    )
    succeedFor(
      hof"∃X ((R(a) ∧ ∃x X(x)) ∨ ((∃y R(y)) ∨ X(b)))",
      Substitution(X -> le"λt ⊤")
    )
    succeedFor(
      hof"∃X ∀x (R(a) ∨ X(x) ∨ R(b))",
      Substitution(X -> le"λt ¬R(a) ∧ ¬R(b)")
    )
    succeedFor(
      hof"∃X (∀x ∃y X(x))",
      Substitution(X -> le"λt ∃x x=t")
    )
    succeedFor(
      hof"∃X (∀x (P(x) -> X(x)))",
      Substitution(X -> le"P:i>o")
    )
    succeedFor(hof"∃X (¬X(a, b) ∧ ∀x ∃y X(x, y))", Substitution(hov"X:i>i>o" -> le"λt_1 λt_2 (t_1 != a ∨ t_2 != b)"))
    succeedFor(hof"∃X ∀x ∃y X(x,y)", Substitution(hov"X:i>i>o" -> le"λt_1 λt_2 ⊤"))
    succeedFor(hof"∃X ∀x (X(x) ∧ R(x))", Substitution(X -> le"λt ∃x x=t"))
    succeedFor(hof"∃X ∀x (X(f(x)) ∨ R(x))", Substitution(X -> le"λt ∃x (t=f(x) ∧ ¬R(x))"))
    succeedFor(hof"∃X X(a, P:o)", Substitution(hov"X:i>o>o" -> le"λ(t:i) λ(p:o) t=a ∧ p=P"))
    extractCorrectly(hof"∃X X(a, P:o)", hof"X(a, P:o)")
    succeedFor(hof"∃X ∃x X(x)", Substitution(X -> le"λt ⊤"))
    succeedFor(hof"∃X !x (X(a,x) ∨ X(b,x))", Substitution(hov"X:i>i>o", le"λt_1 λt_2 ⊤"))
    failFor(hof"∃X ∀x (X(x,a) ∨ ∀y ¬X(x, y))")
    failFor(hof"∃X ((∀x ∃y X(x, y)) ∧ (∀x ∃y ¬X(y, x)))")
    succeedFor(hof"∃X ((¬X(a) ∨ ¬X(b)) ∧ (X(c) ∨ X(d)))", Substitution(X -> le"λt (a!=c ∨ b!=c -> t=c) ∧ (a=c ∧ b=c ∧ (a!=d ∨ b!=d) -> t=d)"))
    succeedFor(hof"∃X ((X(a) ∧ R(b)) ∨ R(c))", Substitution(X -> le"λt ¬R(c)"))
    succeedFor(hof"∃X ((X(a) ∨ R(b)) ∧ (X(c) ∨ S(d)))", Substitution(X -> le"λt (t=a ∧ ¬R(b)) ∨ (t=c ∧ ¬S(d))"))
    succeedFor(hof"∃X (X(a) ∧ ¬X(b))", Substitution(X -> le"λt t=a"))
    succeedFor(hof"∃X X", Substitution(hov"X:o" -> le"⊤"))
  }

  "solveFormulaEquation" should {
    def succeedFor(formulaEquation: Formula): Fragment = {
      s"succeed for $formulaEquation" in {
        solveFormulaEquation(formulaEquation) must beSuccessfulTry
      }
    }

    def failFor(formulaEquation: Formula): Fragment = {
      s"fail for $formulaEquation" in {
        solveFormulaEquation(formulaEquation) must beFailedTry
      }
    }

    failFor(hof"R(a)")
    succeedFor(hof"X(a)")
    failFor(hof"X(a) ∧ ¬X(b)")
    succeedFor(hof"X(c) -> P(c)")
    failFor(hof"¬X(c) ∧ P(c)")
    succeedFor(hof"X(a) ∨ P(a)")
    failFor(hof"(X(a) ∧ ¬X(f(b))) ∨ (X(f(b)) ∧ ¬X(a))")
    succeedFor(hof"X(a) ∧ X(b)")
    succeedFor(hof"X(a) ∨ X(b)")
    succeedFor(hof"¬X(a) -> X(b)")
    failFor(hof"R(a) ∧ X(b)")
    succeedFor(hof"X(a) ∧ Y(b)")
    succeedFor(hof"X(a,b)")
    failFor(hof"(∀x (X(x) -> #c(R:i>o)(x))) ∧ X(a)")
    succeedFor(hof"(∀x (X(x) -> #v(R:i>o)(x))) ∧ X(a)")
    failFor(hof"(∀x (X(x) -> (∀y R(x, y)))) ∧ X(a)")
    failFor(hof"(∀x (X(x) -> R(x))) ∧ (X(a) ∨ X(b))")
    failFor(hof"(∀x (X(x) -> (∀y R(x, y)))) ∧ (X(a) ∨ X(b))")
    failFor(hof"∀x ((∀y R(x,y)) -> X(x)) ∧ (¬X(a) ∨ ¬X(b))")
    failFor(hof"∀x ∀y (R(x,y) -> X(x)) ∧ (¬X(a) ∨ ¬X(b))")
    failFor(hof"∀x ∀y (X(x, y) -> R(x, y)) ∧ (X(a, b) ∨ X(b, c))")
    failFor(hof"∀x ((∀y R(x,y)) -> X(x)) ∧ (X(a) ∨ ¬X(b)) ∧ ¬X(c)")
    succeedFor(hof"∀x (X(x) ∨ R(x))")
    succeedFor(hof"X(a) ∧ ∃x X(x)")
    failFor(hof"(∃x X(x)) ∧ ¬R(a)")
    succeedFor(hof"∃x X(x,a)")
    succeedFor(hof"(R(a) ∧ ∃x X(x)) ∨ ((∃y R(y)) ∨ X(b))")
    succeedFor(hof"∀x (R(a) ∨ X(x) ∨ R(b))")
    succeedFor(hof"∀x ∃y X(x)")
    succeedFor(hof"∀x (P(x) -> X(x))")
    failFor(hof"¬X(a, b) ∧ ∀x ∃y X(x, y)")
    succeedFor(hof"∀x ∃y X(x,y)")
    failFor(hof"∀x (X(x) ∧ R(x))")
    succeedFor(hof"∀x (X(f(x)) ∨ R(x))")
    succeedFor(hof"X(a, P:o)")
    succeedFor(hof"∃x X(x)")
    succeedFor(hof"!x (X(a,x) ∨ X(b,x))")
    failFor(hof"∀x (X(x,a) ∨ ∀y ¬X(x, y))")
    failFor(hof"(∀x ∃y X(x, y)) ∧ (∀x ∃y ¬X(y, x))")
    failFor(hof"(¬X(a) ∨ ¬X(b)) ∧ (X(c) ∨ X(d))")
    failFor(hof"(X(a) ∧ R(b)) ∨ R(c)")
    succeedFor(hof"(X(a) ∨ R(b)) ∧ (X(c) ∨ S(d))")
    failFor(hof"X(a) ∧ ¬X(b)")
  }

  private def beSetEqualsWithCustomEquality[A](
      expectedSet: Set[A],
      equals: (A, A) => Boolean
  ): Matcher[Set[A]] = (thisSet: Set[A]) => {
    val inExpectedAndNotInThis = expectedSet.filterNot(x => thisSet.exists(equals(x, _)))
    val inThisAndNotInExpected = thisSet.filterNot(x => expectedSet.exists(equals(x, _)))
    val errorMessage =
      s"""
         |$thisSet is not equal to $expectedSet according to the given equality
         |Expected, but not present:
         |${inExpectedAndNotInThis.mkString("\n")}
         |
         |Unexpected, but present:
         |${inThisAndNotInExpected.mkString("\n")}
    """.stripMargin
    val areEqual = inExpectedAndNotInThis.isEmpty && inThisAndNotInExpected.isEmpty
    (areEqual, errorMessage)
  }

  private def beAnEquivalentSubstitutionTo(
      equivalentSubstitution: Substitution
  ): Matcher[(Substitution, Formula)] = {
    (input: (Substitution, Formula)) =>
      {
        val (substitution, firstOrderPart) = input
        val substitutedFormula = simplifyPropositional(BetaReduction.betaNormalize(
          substitution(firstOrderPart)
        ))
        val equivalentSubstitutedFormula = simplifyPropositional(BetaReduction.betaNormalize(
          equivalentSubstitution(firstOrderPart)
        ))
        val isValid = Escargot isValid Iff(substitutedFormula, equivalentSubstitutedFormula)
        val errorMessage =
          s"""|applying $substitution is not equivalent to applying $equivalentSubstitution to $firstOrderPart
            |applying $substitution
            |gives $substitutedFormula
            |applying $equivalentSubstitution
            |gives $equivalentSubstitutedFormula
          """.stripMargin
        (isValid, errorMessage)
      }
  }
}
