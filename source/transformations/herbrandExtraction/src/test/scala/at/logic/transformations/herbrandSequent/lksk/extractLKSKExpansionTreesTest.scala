package at.logic.transformations.herbrandSequent.lksk

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.calculi.lk._
import at.logic.language.hol._
import at.logic.calculi.lk.base.{FSequent, Sequent}
import at.logic.language.lambda.types.{Ti, To}
import at.logic.calculi.lksk
import at.logic.transformations.herbrandExtraction.lksk.extractLKSKExpansionTrees
import at.logic.calculi.expansionTrees.{Atom => AtomTree, Neg => NegTree, SkolemQuantifier, ExpansionTree, ExpansionSequent, WeakQuantifier, Imp => ImpTree}
import at.logic.calculi.lksk.LabelledFormulaOccurrence
import at.logic.transformations.skolemization.lksk.{LKtoLKskc => skolemize }

/**
 * Created by marty on 8/7/14.
 */
@RunWith(classOf[JUnitRunner])
class extractLKSKExpansionTreesTest extends SpecificationWithJUnit {
  object simpleHOLProof {
    val p = Atom(HOLConst("P", To), Nil)
    val x = HOLVar("X", To)
    val xatom = Atom(x, Nil)
    val existsx = ExVar(x,xatom)

    val ax = Axiom(List(p), List(p))
    val i1 = ExistsRightRule(ax, ax.root.succedent(0), existsx, p)
    val i2 = NegRightRule(i1, i1.root.antecedent(0))
    val i3 = ExistsRightRule(i2, i2.root.succedent(1), existsx, Neg(p))
    val i4 = ContractionRightRule(i3, i3.root.succedent(0), i3.root.succedent(1))
    val proof = skolemize(i4)
  }

  object simpleLKSKProof {
    val p = Atom(HOLConst("P", To), Nil)
    val x = HOLVar("X", To)
    val xatom = Atom(x, Nil)
    val existsx = ExVar(x,xatom)

    val (ax,_) = lksk.Axiom.createDefault(FSequent(List(p), List(p)), (List(Set(Neg(p))), List(Set(p))) )
    val i1 = lksk.ExistsSkRightRule(ax, ax.root.succedent(0).asInstanceOf[LabelledFormulaOccurrence], existsx, p, true )
    val i2 = NegRightRule(i1, i1.root.antecedent(0))
    val i3 = lksk.ExistsSkRightRule(i2, i2.root.succedent(1).asInstanceOf[LabelledFormulaOccurrence], existsx, Neg(p), true)
    val i4 = ContractionRightRule(i3, i3.root.succedent(0), i3.root.succedent(1))
  }


  object simpleHOLProof2 {
    val x = HOLVar("X", Ti -> To)
    val a = HOLVar("\\alpha", Ti)
    val u = HOLVar("u", Ti)

    val p = HOLConst("P", Ti -> To)
    val pa = Atom(p, List(a))
    val pu = Atom(p, List(u))
    val xatoma = Atom(x, List(a))
    val xatomu = Atom(x, List(u))

    val existsx = ExVar(x,xatoma)
    val alluexistsx = AllVar(u,ExVar(x,xatomu))

    val ax = Axiom(List(pa), List(pa))
    val i1 = ExistsRightRule(ax, ax.root.succedent(0), existsx, HOLAbs(u,pu) )
    val i2 = NegRightRule(i1, i1.root.antecedent(0))
    val i3 = ExistsRightRule(i2, i2.root.succedent(1), existsx, HOLAbs(u, Neg(pu)))
    val i4 = ContractionRightRule(i3, i3.root.succedent(0), i3.root.succedent(1))
    val i5 = ForallRightRule(i4, i4.root.succedent(0), alluexistsx, a)

    val proof = skolemize(i5)
  }

  object simpleHOLProof3 {
    val p = HOLConst("P", Ti -> To)
    val a = HOLVar("\\alpha", Ti)
    val u = HOLVar("u", Ti)

    val pa = Atom(p, a::Nil)
    val pu = Atom(p, u::Nil)
    val allpu = AllVar(u, pu)

    val x = HOLVar("X", To)
    val xatom = Atom(x, Nil)
    val existsx = ExVar(x,xatom)

    val ax = Axiom(List(pa), List(pa))
    val i0a = ForallLeftRule(ax, ax.root.antecedent(0), allpu, a)
    val i0b = ForallRightRule(i0a, i0a.root.succedent(0), allpu, a)
    val i1 = ExistsRightRule(i0b, i0b.root.succedent(0), existsx, allpu)
    val i2 = NegRightRule(i1, i1.root.antecedent(0))
    val i3 = ExistsRightRule(i2, i2.root.succedent(1), existsx, Neg(allpu))
    val i4 = ContractionRightRule(i3, i3.root.succedent(0), i3.root.succedent(1))
    val proof = skolemize(i4)
  }


  object simpleHOLProof4 {
    val p = HOLConst("P", Ti -> To)
    val a = HOLVar("\\alpha", Ti)
    val u = HOLVar("u", Ti)

    val pa = Atom(p, a::Nil)
    val pu = Atom(p, u::Nil)
    val allpu = AllVar(u, pu)

    val x = HOLVar("X", To)
    val xatom = Atom(x, Nil)
    val existsx = ExVar(x,xatom)

    val ax = Axiom(List(pa), List(pa))
    val i0a = ForallLeftRule(ax, ax.root.antecedent(0), allpu, a)
    val i0b = ForallRightRule(i0a, i0a.root.succedent(0), allpu, a)
    val i1 = ExistsRightRule(i0b, i0b.root.succedent(0), existsx, allpu)
    val i2 = NegRightRule(i1, i1.root.antecedent(0))
    val i2a = WeakeningLeftRule(i2, allpu)
    val i2b = ImpRightRule(i2a, i2a.root.antecedent(0), i2a.root.succedent(1))
    val i3 = ExistsRightRule(i2b, i2b.root.succedent(1), existsx, Imp(allpu, Neg(allpu)) )
    val i4 = ContractionRightRule(i3, i3.root.succedent(0), i3.root.succedent(1))
    val proof = skolemize(i4)
  }




  "LKSK Expansion Tree Extraction" should {
    "work for an hol proof with only weak quantifiers" in {

      val et = extractLKSKExpansionTrees(simpleHOLProof.i4, false)

      val inst1 : (ExpansionTree, HOLFormula) = (AtomTree(simpleHOLProof.p), simpleHOLProof.p)
      val inst2 : (ExpansionTree, HOLFormula) = (NegTree(AtomTree(simpleHOLProof.p)), Neg(simpleHOLProof.p))
      val cet : ExpansionTree = WeakQuantifier(simpleHOLProof.existsx, List(inst1, inst2)).asInstanceOf[ExpansionTree] //TODO: this cast is ugly

      val control = ExpansionSequent(Nil, List(cet))

      et must_==(control)
    }

    "work for the same hol proof, automatically skolemized" in {
      val ExpansionSequent((Nil, List(et))) = extractLKSKExpansionTrees(simpleHOLProof.proof, false)

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
      val ExpansionSequent((Nil, List(et))) = extractLKSKExpansionTrees(simpleLKSKProof.i4, false)

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
      val ExpansionSequent((Nil, List(et))) = extractLKSKExpansionTrees(simpleHOLProof2.proof, false)

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
      val ExpansionSequent((Nil, List(et))) = extractLKSKExpansionTrees(simpleHOLProof3.proof, false)

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
      val ExpansionSequent((Nil, List(et))) = extractLKSKExpansionTrees(simpleHOLProof4.proof, false)

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
