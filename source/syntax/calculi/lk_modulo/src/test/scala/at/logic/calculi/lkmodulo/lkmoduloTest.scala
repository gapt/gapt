package at.logic.calculi.lkmodulo

import _root_.at.logic.language.lambda.typedLambdaCalculus.{App, Var, LambdaExpression}
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.scalatest.matchers.MustMatchers
import _root_.at.logic.calculi.proofs.UnaryRuleTypeA
import _root_.at.logic.language.fol._
import _root_.at.logic.language.hol.logicSymbols.{ConstantStringSymbol, ConstantSymbolA}
import _root_.at.logic.language.lambda.substitutions.Substitution
import _root_.at.logic.language.lambda.symbols.VariableStringSymbol
import scala.None
import at.logic.language.fol.{Utils => FOLUtils }
import org.specs2.execute.Success

@RunWith(classOf[JUnitRunner])
class LKModuloTest extends SpecificationWithJUnit {
  /*
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

      Renaming.canonical_renaming_of(f1) match {
        case Atom(_, List(e1,e2,e3)) =>
          e1 must_!= e2
          e1 must_!= e3
          e2 must_!= e3
          e1.toString().substring(0,2) must beEqualTo("x_")
          e1.toString().substring(0,2) must beEqualTo("x_")
          e1.toString().substring(0,2) must beEqualTo("x_")
        case _ => "canonical renaming of an atom formula must stay an atom formula" must beEqualTo ("")
      }

      Renaming.canonical_renaming_of(f1).toString() must beEqualTo (Renaming.canonical_renaming_of(f1b).toString())
    }

  "have proper normalization (2)" in {
    val ps = new ConstantStringSymbol("R")
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
    println(FOLUtils.isPredicateType(Atom(ps, List(FOLVar(xs), FOLVar(ys))).exptype))

    Atom(ps, List(FOLVar(xs), FOLVar(ys))).asInstanceOf[LambdaExpression] match {
      case App(exp1, exp2) =>
        println("bla "+exp1.exptype)
        println("bli "+exp2.exptype)
    }


    Renaming.canonical_renaming_of(f2) match {
      case And(Neg(Atom(ps,List(FOLVar(e1)))),
                AllVar(FOLVar(e2), (AllVar(FOLVar(e3),
                  Atom(p, List(FOLVar(e4))))))) =>
        p must_== ps
        e1 must_!= e2
        e1 must_!= e3
        e2 must_!= e3
        e3 must_== e4

      case _ => "the structure of a formula must stay the same during canonical renaming" must beEqualTo ("")
    }
    Renaming.canonical_renaming_of(f2).toString() must beEqualTo (Renaming.canonical_renaming_of(f2b).toString())

    println (Renaming.canonical_renaming_of(f2.asInstanceOf[LambdaExpression]))
    println (Renaming.fol_as_tptp(f2))
    println (TPTP((List(f2,f2b))))
  }

  "have proper tptp export" in {
    val ps = new ConstantStringSymbol("R")
    val as = FOLConst(new ConstantStringSymbol("a"))
    val bs = FOLConst(new ConstantStringSymbol("b"))
    val xs = FOLVar(new VariableStringSymbol("x"))
    val ys = FOLVar(new VariableStringSymbol("y"))
    val zs = FOLVar(new VariableStringSymbol("z") )
    val f1 = Atom(ps, List(as,bs))
    val f2 = And(Atom(ps,List(as,as)), AllVar(xs,AllVar(ys,Imp(Atom(ps,List(xs,ys)), Atom(ps,List(xs,xs))) )))
    println(TPTP(List(f1), List(f2)))
    // specs2 require a least one Result, see org.specs2.specification.Example 
    Success()
  }
*/
}
