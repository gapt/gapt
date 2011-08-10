package at.logic.calculi.lkmodulo

import _root_.at.logic.language.lambda.typedLambdaCalculus.{Var, LambdaExpression}
import org.specs.SpecificationWithJUnit
import org.scalatest.matchers.MustMatchers

import _root_.at.logic.calculi.proofs.UnaryRuleTypeA
import _root_.at.logic.language.fol._
import _root_.at.logic.language.fol.equations.Equation
import _root_.at.logic.language.hol.logicSymbols.{ConstantStringSymbol, ConstantSymbolA}
import _root_.at.logic.language.lambda.substitutions.Substitution
import _root_.at.logic.language.lambda.symbols.VariableStringSymbol
import _root_.at.logic.language.lambda.types.->
import at.logic.calculi.lk.base.LKProof
import at.logic.calculi.lk._
import scala.None


class LKModuloTest extends SpecificationWithJUnit {
    class TestEEquality extends EequalityA {
        def unifies_with(s: FOLTerm, t: FOLTerm) : Option[Substitution[FOLTerm]] = {
          None
        }

      val equational_rules : Set[Equation] = Set()
      def word_equalsto(s : FOLTerm, t : FOLTerm) : Boolean = true

    }

    "have proper normalization (1)" in {
      val ps = new ConstantStringSymbol("P")
      val xs = new VariableStringSymbol("x")
      val ys = new VariableStringSymbol("y")
      val zs = new VariableStringSymbol("z")
      val f1 = Atom(ps, List(FOLVar(xs),FOLVar(ys),FOLVar(zs)))
      val f1b = Atom(ps, List(FOLVar(zs),FOLVar(xs),FOLVar(ys)))
      val eq = new TestEEquality()

      eq.canonical_renaming_of(f1) match {
        case Atom(_, List(e1,e2,e3)) =>
          e1 mustNotEq e2
          e1 mustNotEq e3
          e2 mustNotEq e3
          e1.toString().substring(0,2) must beEqual("x_")
          e1.toString().substring(0,2) must beEqual("x_")
          e1.toString().substring(0,2) must beEqual("x_")
        case _ => "canonical renaming of an atom formula must stay an atom formula" must beEqual ("")
      }

      eq.canonical_renaming_of(f1).toString() must beEqual (eq.canonical_renaming_of(f1b).toString())
    }

  "have proper normalization (2)" in {
    val ps = new ConstantStringSymbol("P")
    val xs = new VariableStringSymbol("x")
    val ys = new VariableStringSymbol("y")
    val zs = new VariableStringSymbol("z")
    val f2 = And(Neg(Atom(ps,List(FOLVar(xs)))),
                AllVar(FOLVar(ys), (AllVar(FOLVar(xs),
                  Atom(ps, List(FOLVar(xs))))))) //f2 == "-P(x) & all y all x P(x)"
    val f2b = And(Neg(Atom(ps,List(FOLVar(zs)))),
                AllVar(FOLVar(zs), (AllVar(FOLVar(ys),
                  Atom(ps, List(FOLVar(ys)))))))
    val eq = new TestEEquality()

    eq.canonical_renaming_of(f2) match {
      case And(Neg(Atom(ps,List(FOLVar(e1)))),
                AllVar(FOLVar(e2), (AllVar(FOLVar(e3),
                  Atom(p, List(FOLVar(e4))))))) =>
        p mustEq ps
        e1 mustNotEq e2
        e1 mustNotEq e3
        e2 mustNotEq e3
        e3 mustEq  e4

      case _ => "the structure of a formula must stay the same during canonical renaming" must beEqual ("")
    }
    eq.canonical_renaming_of(f2).toString() must beEqual (eq.canonical_renaming_of(f2b).toString())
  }

}
