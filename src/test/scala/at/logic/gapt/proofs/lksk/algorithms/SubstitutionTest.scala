package at.logic.gapt.proofs.lksk.algorithms

import at.logic.gapt.language.hol._
import at.logic.gapt.language.lambda.types._
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.proofs.lksk.TypeSynonyms._
import at.logic.gapt.proofs.lksk._
import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class SubstitutionTest extends SpecificationWithJUnit {
  "Substitutions" should {
    val f = HOLConst("f", Ti -> Ti)
    val y = HOLVar("y", Ti)
    val x = HOLVar("x", Ti)
    val a = HOLVar("a", Ti)
    val fa = HOLApp(f, a)
    val R = HOLConst("R", Ti -> (Ti -> To))
    val Rafa = HOLAtom(R, a::fa::Nil)
    val exyRay = HOLExVar(y, HOLAtom(R, a::y::Nil ))
    val allxexy = HOLAllVar(x, HOLExVar( y, HOLAtom(R, x::y::Nil ) ) )

    val ax = Axiom.createDefault(new FSequent(Rafa::Nil, Rafa::Nil), Tuple2( (EmptyLabel() + a)::Nil , EmptyLabel()::Nil ) )
    val r1 = ExistsSkLeftRule(ax._1, ax._2._1.head, exyRay, fa)
    val r2 = ForallSkLeftRule(r1, r1.prin.head, allxexy, a, true)
    r2.root.antecedent.toList.head must beLike {case o: LabelledFormulaOccurrence => ok}
    r2.root.succedent.toList.head must beLike {case o: LabelledFormulaOccurrence => ok}

    "work for an axiom" in {
      val P = HOLConst("P", Ti -> To)
      val Px = HOLAtom(P, x::Nil)
      val c : HOLExpression = HOLConst("c", Ti)
      val Pc = HOLAtom(P, c::Nil)

      val a = Axiom.createDefault(new FSequent( Px::Nil, Px::Nil ), Tuple2( (EmptyLabel() + x)::Nil, (EmptyLabel() + y)::Nil ) )
      val subst = Substitution(x, c)
      val r = applySubstitution(a._1, subst)
      r._1.root.succedent.toList.head must beLike {case o : LabelledFormulaOccurrence => o.skolem_label == (EmptyLabel() + y) && o.formula == Pc must_== true }
      r._1.root.antecedent.toList.head must beLike {case o : LabelledFormulaOccurrence => o.skolem_label == (EmptyLabel() + c) && o.formula == Pc must_== true }
    }

    "apply correctly to a simple proof" in {
      val c = HOLConst("c", Ti)
      val g = HOLConst("g", Ti -> Ti)
      val gc = HOLApp(g, c)
      val fgc = HOLApp(f, gc)
      val R = HOLConst("R", Ti -> (Ti -> To))
      val Rgcfgc = HOLAtom(R, gc::fgc::Nil )
      val exyRgcy = HOLExVar(y, HOLAtom(R, gc::y::Nil ) )
      val subst = Substitution( a, gc ) // a <- g(c)

      val p_s = applySubstitution( r2, subst )
      p_s._1.root.antecedent.toList.head must beLike{ case o : LabelledFormulaOccurrence => o.skolem_label == EmptyLabel() && o.formula == allxexy must_== true }
      p_s._1.root.succedent.toList.head must beLike{ case o : LabelledFormulaOccurrence => o.skolem_label == EmptyLabel() && o.formula == Rgcfgc must_== true }
    }
  }
}
