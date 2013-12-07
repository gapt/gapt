
package at.logic.calculi.expansionTrees

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.hol.{Atom => AtomHOL, And => AndHOL, Or => OrHOL, Imp => ImpHOL, _}
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.substitutions._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.hol.logicSymbols._


@RunWith(classOf[JUnitRunner])
class ExpansionTreeTest extends SpecificationWithJUnit {

  val c = HOLConst(ConstantStringSymbol("c" ), i)
  val d = HOLConst(ConstantStringSymbol("d" ), i)
  val x = HOLVar(VariableStringSymbol("x" ), i)
  val y = HOLVar(VariableStringSymbol("y" ), i)
  val z = HOLVar(VariableStringSymbol("z" ), i)
  val eq = new ConstantStringSymbol("=")
  val P = new ConstantStringSymbol("P")

  val et1 = WeakQuantifier(
    ExVar(x, AtomHOL(eq, x::x::Nil)),
    List((Atom( AtomHOL(eq, c::c::Nil) ) , c))
  )

  val et2 = WeakQuantifier(
    ExVar(x, AtomHOL(P, x::y::c::Nil)),
    List((Atom( AtomHOL(P, z::y::c::Nil) ), z))
  )

  val et3 = StrongQuantifier(
    AllVar(x, AtomHOL(P, x::d::z::Nil)),
    z,
    Atom( AtomHOL(P, z::d::z::Nil) )
  )

  val et4 = WeakQuantifier(
    ExVar(x, AtomHOL(P, x::c::Nil)),
    List(
      (Atom( AtomHOL(P, z::c::Nil) ), z),
      (Atom( AtomHOL(P, y::c::Nil) ), y)
    )
  )

  "Expansion Trees substitution" should {

    "replace variables correctly 1" in {
      val s = Substitution[HOLExpression](y, d)
      val etPrime = substitute(s, et2)

      etPrime mustEqual WeakQuantifier(
        ExVar(x, AtomHOL(P, x :: d :: c :: Nil)),
        List((Atom(AtomHOL(P, z :: d :: c :: Nil)), z))
      )
    }

    "replace variables correctly 2" in {
      val s = Substitution[HOLExpression](z, d)
      val etPrime = substitute(s, et2)

      etPrime mustEqual WeakQuantifier(
        ExVar(x, AtomHOL(P, x :: y :: c :: Nil)),
        List((Atom(AtomHOL(P, d :: y :: c :: Nil)), d))
      )
    }

    "replace variables correctly 3" in {
      val s = Substitution[HOLExpression](z, y)
      val etPrime = substitute(s, et3)

      etPrime mustEqual StrongQuantifier(
        AllVar(x, AtomHOL(P, x::d::y::Nil)),
        y,
        Atom( AtomHOL(P, y::d::y::Nil) )
      )
    }

    "not replace const " in {
      val s = Substitution[HOLExpression](HOLVar(new VariableStringSymbol("c"), i), HOLConst(new ConstantStringSymbol("d"), i))
      val etPrime = substitute(s, et1)

      etPrime mustEqual et1
    }

    "create merge node in case of collapse in weak quantifier instances " in {
      val s = Substitution[HOLExpression](z, y)
      val etPrime = substitute.applyNoMerge(s, et4)


        etPrime mustEqual WeakQuantifier(
        ExVar(x, AtomHOL(P, x::c::Nil)),
        List(
          (MergeNode(Atom(AtomHOL(P, y::c::Nil)), Atom(AtomHOL(P, y::c::Nil))), y)
        )
      )

    }

  }

}


