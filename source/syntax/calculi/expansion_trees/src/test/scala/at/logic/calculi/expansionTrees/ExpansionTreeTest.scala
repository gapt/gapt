
package at.logic.calculi.expansionTrees

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.hol.{Atom => AtomHOL, And => AndHOL, Or => OrHOL, Imp => ImpHOL, _}
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.substitutions._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.lk.propositionalRules.{ContractionLeftRule, Axiom}
import at.logic.calculi.lk.quantificationRules.{ExistsLeftRule, ExistsRightRule}


@RunWith(classOf[JUnitRunner])
class ExpansionTreeTest extends SpecificationWithJUnit {

  val alpha = HOLVar(VariableStringSymbol("\\alpha" ), i)
  val beta = HOLVar(VariableStringSymbol("\\beta" ), i)
  val c = HOLConst(ConstantStringSymbol("c" ), i)
  val d = HOLConst(ConstantStringSymbol("d" ), i)
  val f = ConstantStringSymbol("f")
  val x = HOLVar(VariableStringSymbol("x" ), i)
  val y = HOLVar(VariableStringSymbol("y" ), i)
  val z = HOLVar(VariableStringSymbol("z" ), i)
  val eq = new ConstantStringSymbol("=")
  val P = new ConstantStringSymbol("P")
  val Q = new ConstantStringSymbol("Q")

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

  "Expansion Trees merge" should {
    "merge identical trees" in {
      merge(MergeNode(et4, et4)) mustEqual( et4 )
    }

    "do simple substitution as result of merge" in {
      val etSubst1 = Neg( StrongQuantifier(AllVar(x, AtomHOL(P, x::Nil) ), z, Atom( AtomHOL(P, z::Nil)) ) )
      val etSubst2 = Neg( StrongQuantifier(AllVar(x, AtomHOL(P, x::Nil) ), y, Atom( AtomHOL(P, y::Nil)) ) )

      // from a theoretical point of view, the result could also be equal to the second tree, but users probably expect the algo to work from left to right
      merge( MergeNode(etSubst1, etSubst2) ) mustEqual etSubst1
    }

    "do simple substitution as result of merge with context" in {
      val etSubst1 = Neg( StrongQuantifier(AllVar(x, AtomHOL(P, x::Nil) ), z, Atom( AtomHOL(P, z::Nil)) ) )
      val etSubst2 = Neg( StrongQuantifier(AllVar(x, AtomHOL(P, x::Nil) ), y, Atom( AtomHOL(P, y::Nil)) ) )
      merge( MergeNode(etSubst1, etSubst2) ) mustEqual etSubst1
    }

    "do merge with substitution in other tree of sequent triggered by merge" in {
      // example from Chaudhuri et.al : A multi-focused proof system isomorphic to expansion proofs
      val etSubst1 = StrongQuantifier(AllVar(x, AtomHOL(P, x::Nil) ), z, Atom( AtomHOL(P, z::Nil)) )
      val etSubst2 = StrongQuantifier(AllVar(x, AtomHOL(P, x::Nil) ), y, Atom( AtomHOL(P, y::Nil)) )
      val fy = Function(f, y::Nil, i)
      val fz = Function(f, z::Nil, i)
      val seq = (Nil,
        // only succedent:
        MergeNode(etSubst1, etSubst2) ::
        WeakQuantifier(ExVar(x, AtomHOL(Q, x::Nil)), List(
          (Atom(AtomHOL(Q, fz::Nil)), fz ),
          (Atom(AtomHOL(Q, fy::Nil)), fy )
        )) ::
        Atom( AtomHOL(P, z::Nil) ) ::
        Atom( AtomHOL(P, y::Nil) ) ::
        Nil
        )
      val mergedSeq = merge(seq)

      // merge will trigger a substitution y -> z

      val testResult = new ExpansionSequent(Nil,
        (StrongQuantifier(AllVar(x, AtomHOL(P, x::Nil)), z, Atom( AtomHOL(P, z::Nil))) ::
        WeakQuantifier(ExVar(x, AtomHOL(Q, x::Nil)), List( (Atom(AtomHOL(Q, fz::Nil)), fz))) ::
        Atom( AtomHOL(P, z::Nil) ) ::
        Atom( AtomHOL(P, z::Nil) ) ::
        Nil).asInstanceOf[Seq[ExpansionTree]]
      )

      mergedSeq mustEqual testResult
    }



  }

}


