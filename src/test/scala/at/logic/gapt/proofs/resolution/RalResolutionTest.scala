package at.logic.gapt.proofs.resolution.ral

import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.proofs.lksk.LabelledSequent
import at.logic.gapt.proofs.lksk.TypeSynonyms.{Label, EmptyLabel}
import at.logic.gapt.language.hol._
import at.logic.gapt.language.lambda.types.{Ti, To}
import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner

/**
 * Created by marty on 9/10/14.
 */
@RunWith(classOf[JUnitRunner])
class RalResolutionTest extends SpecificationWithJUnit{
  "Ral resolution" should {
    "work on simple proofs" in {
      val x = HOLVar("X", To)
      val p = HOLAtom(HOLConst("P", To), Nil)
      val exx = HOLExVar(x,x.asInstanceOf[HOLFormula])
      val root = FSequent(Nil,List(exx))
      val labels : (List[Label],List[Label]) = (List[Label](),List[Label](EmptyLabel()))

      val i1 = InitialSequent(root, labels)
      val i2 = ForallT(i1, i1.root.l_succedent(0), x)
      val i3 = Sub(i2, Substitution(x, HOLAnd(p, HOLNeg(p))))
      val i4 = AndT1(i3, i3.root.l_succedent(0))
      val i5 = AndT2(i3, i3.root.l_succedent(0))
      val i6 = NegT(i5, i5.root.l_succedent(0))
      val i7 = Cut(i4,i6,List(i4.root.l_succedent(0)), List(i6.root.l_antecedent(0)))

      i7.root.toFSequent must_== (FSequent(Nil,Nil))
      ok
    }

    "work on non-idempotent substitutions" in {
      val x = HOLVar("x", Ti)
      val fx = HOLFunction(HOLConst("f", Ti -> Ti), x::Nil)
      val px = HOLAtom(HOLConst("P", Ti->To), List(x))
      val pfx = HOLAtom(HOLConst("P", Ti->To), List(fx))

      val sub = Substitution(x, fx)

      val root = FSequent(Nil,List(px))
      val labels : (List[Label],List[Label]) = (List[Label](),List[Label](EmptyLabel()))

      val i1 = InitialSequent(root, labels)
      val i2 = Sub(i1,sub)
      i2.root.succedent(0).formula must_== (pfx)
      ok
    }
  }

}
