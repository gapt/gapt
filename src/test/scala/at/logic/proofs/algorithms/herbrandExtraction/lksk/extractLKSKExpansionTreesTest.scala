package at.logic.proofs.algorithms.herbrandExtraction.lksk

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.proofs.lk._
import at.logic.language.hol._
import at.logic.proofs.lk.base.{FSequent, Sequent}
import at.logic.language.lambda.types.{Ti, To}
import at.logic.proofs.lksk
import at.logic.proofs.expansionTrees.{Atom => AtomTree, Neg => NegTree, SkolemQuantifier, ExpansionTree, ExpansionSequent, WeakQuantifier, Imp => ImpTree}
import at.logic.proofs.lksk.LabelledFormulaOccurrence
import at.logic.proofs.algorithms.skolemization.lksk.{LKtoLKskc => skolemize }

/**
 * Created by marty on 8/7/14.
 */
@RunWith(classOf[JUnitRunner])
class extractLKSKExpansionSequentTest extends SpecificationWithJUnit {
  object simpleHOLProof {
    val p = HOLAtom(HOLConst("P", To), Nil)
    val x = HOLVar("X", To)
    val xatom = HOLAtom(x, Nil)
    val existsx = HOLExVar(x,xatom)

    val ax = Axiom(List(p), List(p))
    val i1 = ExistsRightRule(ax, ax.root.succedent(0), existsx, p)
    val i2 = NegRightRule(i1, i1.root.antecedent(0))
    val i3 = ExistsRightRule(i2, i2.root.succedent(1), existsx, HOLNeg(p))
    val i4 = ContractionRightRule(i3, i3.root.succedent(0), i3.root.succedent(1))
    val proof = skolemize(i4)
  }

  object simpleLKSKProof {
    val p = HOLAtom(HOLConst("P", To), Nil)
    val x = HOLVar("X", To)
    val xatom = HOLAtom(x, Nil)
    val existsx = HOLExVar(x,xatom)

    val (ax,_) = lksk.Axiom.createDefault(FSequent(List(p), List(p)), (List(Set(HOLNeg(p))), List(Set(p))) )
    val i1 = lksk.ExistsSkRightRule(ax, ax.root.succedent(0).asInstanceOf[LabelledFormulaOccurrence], existsx, p, true )
    val i2 = NegRightRule(i1, i1.root.antecedent(0))
    val i3 = lksk.ExistsSkRightRule(i2, i2.root.succedent(1).asInstanceOf[LabelledFormulaOccurrence], existsx, HOLNeg(p), true)
    val i4 = ContractionRightRule(i3, i3.root.succedent(0), i3.root.succedent(1))
  }


  object simpleHOLProof2 {
    val x = HOLVar("X", Ti -> To)
    val a = HOLVar("\\alpha", Ti)
    val u = HOLVar("u", Ti)

    val p = HOLConst("P", Ti -> To)
    val pa = HOLAtom(p, List(a))
    val pu = HOLAtom(p, List(u))
    val xatoma = HOLAtom(x, List(a))
    val xatomu = HOLAtom(x, List(u))

    val existsx = HOLExVar(x,xatoma)
    val alluexistsx = HOLAllVar(u,HOLExVar(x,xatomu))

    val ax = Axiom(List(pa), List(pa))
    val i1 = ExistsRightRule(ax, ax.root.succedent(0), existsx, HOLAbs(u,pu) )
    val i2 = NegRightRule(i1, i1.root.antecedent(0))
    val i3 = ExistsRightRule(i2, i2.root.succedent(1), existsx, HOLAbs(u, HOLNeg(pu)))
    val i4 = ContractionRightRule(i3, i3.root.succedent(0), i3.root.succedent(1))
    val i5 = ForallRightRule(i4, i4.root.succedent(0), alluexistsx, a)

    val proof = skolemize(i5)
  }

  object simpleHOLProof3 {
    val p = HOLConst("P", Ti -> To)
    val a = HOLVar("\\alpha", Ti)
    val u = HOLVar("u", Ti)

    val pa = HOLAtom(p, a::Nil)
    val pu = HOLAtom(p, u::Nil)
    val allpu = HOLAllVar(u, pu)

    val x = HOLVar("X", To)
    val xatom = HOLAtom(x, Nil)
    val existsx = HOLExVar(x,xatom)

    val ax = Axiom(List(pa), List(pa))
    val i0a = ForallLeftRule(ax, ax.root.antecedent(0), allpu, a)
    val i0b = ForallRightRule(i0a, i0a.root.succedent(0), allpu, a)
    val i1 = ExistsRightRule(i0b, i0b.root.succedent(0), existsx, allpu)
    val i2 = NegRightRule(i1, i1.root.antecedent(0))
    val i3 = ExistsRightRule(i2, i2.root.succedent(1), existsx, HOLNeg(allpu))
    val i4 = ContractionRightRule(i3, i3.root.succedent(0), i3.root.succedent(1))
    val proof = skolemize(i4)
  }


  object simpleHOLProof4 {
    val p = HOLConst("P", Ti -> To)
    val a = HOLVar("\\alpha", Ti)
    val u = HOLVar("u", Ti)

    val pa = HOLAtom(p, a::Nil)
    val pu = HOLAtom(p, u::Nil)
    val allpu = HOLAllVar(u, pu)

    val x = HOLVar("X", To)
    val xatom = HOLAtom(x, Nil)
    val existsx = HOLExVar(x,xatom)

    val ax = Axiom(List(pa), List(pa))
    val i0a = ForallLeftRule(ax, ax.root.antecedent(0), allpu, a)
    val i0b = ForallRightRule(i0a, i0a.root.succedent(0), allpu, a)
    val i1 = ExistsRightRule(i0b, i0b.root.succedent(0), existsx, allpu)
    val i2 = NegRightRule(i1, i1.root.antecedent(0))
    val i2a = WeakeningLeftRule(i2, allpu)
    val i2b = ImpRightRule(i2a, i2a.root.antecedent(0), i2a.root.succedent(1))
    val i3 = ExistsRightRule(i2b, i2b.root.succedent(1), existsx, HOLImp(allpu, HOLNeg(allpu)) )
    val i4 = ContractionRightRule(i3, i3.root.succedent(0), i3.root.succedent(1))
    val proof = skolemize(i4)
  }




  "LKSK Expansion Tree Extraction" should {
    "work for an hol proof with only weak quantifiers" in {

      val et = extractLKSKExpansionSequent(simpleHOLProof.i4, false)

      val inst1 : (ExpansionTree, HOLFormula) = (AtomTree(simpleHOLProof.p), simpleHOLProof.p)
      val inst2 : (ExpansionTree, HOLFormula) = (NegTree(AtomTree(simpleHOLProof.p)), HOLNeg(simpleHOLProof.p))
      val cet : ExpansionTree = WeakQuantifier(simpleHOLProof.existsx, List(inst1, inst2)).asInstanceOf[ExpansionTree] //TODO: this cast is ugly

      val control = ExpansionSequent(Nil, List(cet))

      et must_==(control)
    }

    "work for the same hol proof, automatically skolemized" in {
      val ExpansionSequent((Nil, List(et))) = extractLKSKExpansionSequent(simpleHOLProof.proof, false)

      val r = et match {
        case WeakQuantifier(_, Seq(
        (AtomTree(_),_),
        (NegTree(AtomTree(_)),_))
        ) =>
          ""
        case _ =>
          "expansion tree "+et+" does not match expected pattern!"
      }

      r must_==("")
    }

    "work for the same hol proof, manually skolemized" in {
      val ExpansionSequent((Nil, List(et))) = extractLKSKExpansionSequent(simpleLKSKProof.i4, false)

      val r = et match {
        case WeakQuantifier(_, Seq(
        (AtomTree(_),_),
        (NegTree(AtomTree(_)),_))
        ) =>
          ""
        case _ =>
          "expansion tree "+et+" does not match expected pattern!"
      }

      r must_==("")
    }

    "work for a skolemized hol proof with strong individual quantifiers" in {
      val ExpansionSequent((Nil, List(et))) = extractLKSKExpansionSequent(simpleHOLProof2.proof, false)

      val r = et match {
        case SkolemQuantifier(_,sk,
          WeakQuantifier(_, Seq(
            (AtomTree(_),_),
            (NegTree(AtomTree(_)),_))
        )) =>
          ""
        case _ =>
          "expansion tree "+et+" does not match expected pattern!"
      }

      r must_==("")
    }

    "work for a skolemized hol proof with strong individual quantifiers inside weak ho quantifiers" in {
      val ExpansionSequent((Nil, List(et))) = extractLKSKExpansionSequent(simpleHOLProof3.proof, false)

      val r = et match {
        case WeakQuantifier(_, Seq(
              (SkolemQuantifier(_,sk1,AtomTree(_)),_),
              (NegTree( WeakQuantifier(_,Seq((AtomTree(_), sk2)))  ), _)
            )) =>
          ""
        case _ =>
          "expansion tree "+et+" does not match expected pattern!"
      }

      r must_==("")
    }

    "work for a skolemized hol proof with weakening" in {
      val ExpansionSequent((Nil, List(et))) = extractLKSKExpansionSequent(simpleHOLProof4.proof, false)

      val r = et match {
        case WeakQuantifier(_, Seq(
        (SkolemQuantifier(_,sk1,AtomTree(_)),_),
        (ImpTree(AtomTree(_), NegTree( WeakQuantifier(_,Seq((AtomTree(_), sk2)))  )), _)
        )) =>
          ""
        case _ =>
          "expansion tree "+et+" does not match expected pattern!"
      }

      r must_==("")
    }
  }

}
