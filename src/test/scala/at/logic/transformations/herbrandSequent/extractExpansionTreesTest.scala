package at.logic.transformations.herbrandSequent

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.lambda.types._
import at.logic.language.hol._
import at.logic.calculi.lk._
import at.logic.transformations.herbrandExtraction._
import at.logic.calculi.expansionTrees.{StrongQuantifier => StrongQuantifierET, WeakQuantifier => WeakQuantifierET, Atom => AtomET, Imp => ImpET}
import at.logic.calculi.lk.base.LKProof
import at.logic.language.fol.{Atom => FOLAtom, Function => FOLFunction, FOLConst, FOLVar, Utils}

@RunWith(classOf[JUnitRunner])
class ExtractExpansionTreesTest extends SpecificationWithJUnit {

  def LinearExampleProof(k: Int, n: Int): LKProof = {
    val s = "s"
    val p = "P"

    val x = FOLVar("x")
    val ass = AllVar(x, Imp(FOLAtom(p, x :: Nil), FOLAtom(p, FOLFunction(s, x :: Nil) :: Nil)))
    if (k == n) {
      val a = FOLAtom(p, Utils.numeral(n) :: Nil)
      WeakeningLeftRule(Axiom(a :: Nil, a :: Nil), ass)
    } else {
      val p1 = FOLAtom(p, Utils.numeral(k) :: Nil)
      val p2 = FOLAtom(p, Utils.numeral(k + 1) :: Nil)
      val aux = Imp(p1, p2)
      ContractionLeftRule(ForallLeftRule(ImpLeftRule(Axiom(p1 :: Nil, p1 :: Nil), LinearExampleProof(k + 1, n), p1, p2), aux, ass, Utils.numeral(k)), ass)
    }
  }


  "The expansion tree extraction" should {

    "handle successive contractions " in {
      val etSeq = extractExpansionSequent(LinearExampleProof(0, 2), false)

      val p = "P"
      val x = FOLVar("x")
      val s = "s"

      val ass = AllVar(x, Imp(FOLAtom(p, x :: Nil), FOLAtom(p, FOLFunction(s, x :: Nil) :: Nil)))

      val equal_permut_1 = etSeq.antecedent equals List(
        AtomET(FOLAtom(p, Utils.numeral(0)::Nil)),
        WeakQuantifierET( ass, List(
          (ImpET( AtomET( FOLAtom(p, Utils.numeral(0)::Nil)), AtomET( FOLAtom(p, Utils.numeral(1)::Nil) ) ), Utils.numeral(0)),
          (ImpET( AtomET( FOLAtom(p, Utils.numeral(1)::Nil)), AtomET( FOLAtom(p, Utils.numeral(2)::Nil) ) ), Utils.numeral(1)))
        )
      )

      val equal_permut_2 = etSeq.antecedent equals List(
        AtomET(FOLAtom(p, Utils.numeral(0)::Nil)),
        WeakQuantifierET( ass, List(
          (ImpET( AtomET( FOLAtom(p, Utils.numeral(1)::Nil)), AtomET( FOLAtom(p, Utils.numeral(2)::Nil) ) ), Utils.numeral(1)),
          (ImpET( AtomET( FOLAtom(p, Utils.numeral(0)::Nil)), AtomET( FOLAtom(p, Utils.numeral(1)::Nil) ) ), Utils.numeral(0)))
        )
      )

      (equal_permut_1 || equal_permut_2) must beTrue

      etSeq.succedent mustEqual( List( AtomET( FOLAtom(p, Utils.numeral(2)::Nil) ) ) )
    }

    "do merge triggering a substitution triggering a merge" in {

      val alpha = HOLVar("\\alpha", Ti)
      val beta = HOLVar("\\beta", Ti)
      val c = HOLConst("c", Ti)
      val d = HOLConst("d", Ti)
      val f = HOLConst("f", Ti->Ti)
      val x = HOLVar("x", Ti)
      val y = HOLVar("y", Ti)
      val z = HOLVar("z", Ti)
      val P = HOLConst("P", Ti->To)
      val Q = HOLConst("Q", Ti->(Ti->To))

      val p0 = Axiom(List(Atom(P, alpha::Nil), Atom(P, beta::Nil)), // P(a), P(b)
                     List(Atom(Q, Function(f, alpha::Nil)::c::Nil), Atom(Q, Function(f, beta::Nil)::d::Nil))) // Q(f(a), c), Q(f(b), d)
      val p1 = ExistsRightRule(p0, Atom(Q, Function(f, alpha::Nil)::c::Nil), ExVar(z, Atom(Q, Function(f, alpha::Nil)::z::Nil)), c)
      val p2 = ExistsRightRule(p1, Atom(Q, Function(f, beta::Nil)::d::Nil), ExVar(z, Atom(Q, Function(f, beta::Nil)::z::Nil)), d)

      val p2_1 = ExistsRightRule(p2, ExVar(z, Atom(Q, Function(f, alpha::Nil)::z::Nil)), ExVar(y, ExVar(z, Atom(Q, y::z::Nil))), Function(f, alpha::Nil))
      val p2_2 = ExistsRightRule(p2_1, ExVar(z, Atom(Q, Function(f, beta::Nil)::z::Nil)), ExVar(y, ExVar(z, Atom(Q, y::z::Nil))), Function(f, beta::Nil))

      val p2_3 = ContractionRightRule(p2_2, ExVar(y, ExVar(z, Atom(Q, y::z::Nil))))

      val p3 = ExistsLeftRule(p2_3, Atom(P, alpha::Nil), ExVar(x, Atom(P, x::Nil)), alpha)
      val p4 = ExistsLeftRule(p3, Atom(P, beta::Nil), ExVar(x, Atom(P, x::Nil)), beta)
      val p5 = ContractionLeftRule(p4, ExVar(x, Atom(P, x::Nil)))

      val (ante, succ) = extractExpansionSequent( p5, false ).toTuple()

      ante mustEqual( List(StrongQuantifierET( ExVar(x, Atom(P, x::Nil)), alpha, AtomET(Atom(P, alpha::Nil)))) )
      // this assumes that the first variable wins, f(beta) would also be valid
      val f_alpha = Function(f, alpha::Nil)
      succ mustEqual( List(WeakQuantifierET(  ExVar(y, ExVar(z, Atom(Q, y::z::Nil)) ),
                            List(
                               (WeakQuantifierET( ExVar(z, Atom(Q, f_alpha::z::Nil)),
                                    List( (AtomET(Atom(Q, f_alpha::c::Nil)), c),
                                          (AtomET(Atom(Q, f_alpha::d::Nil)), d))),
                               f_alpha)
                            )
      )))

    }

    "handle polarity" in {
      val p0 = Axiom(BottomC::Nil, TopC::Nil)
      val p1 = WeakeningRightRule(p0, TopC) // weakened, hence bot on right side
      val p2 = ContractionRightRule(p1, TopC) // polarity is positive, so bottom [merge] top = top
      val p3 = WeakeningLeftRule(p2, BottomC) // weakened, hence top on left side
      val p4 = ContractionLeftRule(p3, BottomC) // negative polarity, bottom must win

      val (ante, succ) = extractExpansionSequent(p4, false).toTuple()
      ante mustEqual AtomET(BottomC)::Nil
      succ mustEqual AtomET(TopC)::Nil
    }

    "handle multiple formulas in axiom" in {
      val s = "s"
      val c = FOLConst("c")
      val d = FOLConst("d")
      val x = FOLVar("x")
      val p = "P"

      val f = AllVar(x, FOLAtom(p, x::Nil))

      val p0_0 = Axiom(FOLAtom(p, c::Nil)::f::Nil, FOLAtom(p, c::Nil)::Nil)

      val p0_1 = Axiom(FOLAtom(p, d::Nil)::Nil, FOLAtom(p, d::Nil)::Nil)
      val p0_2 = ForallLeftRule(p0_1, FOLAtom(p, d::Nil), f, d)

      val p1 = AndRightRule(p0_0, p0_2, FOLAtom(p, c::Nil), FOLAtom(p, d::Nil))
      val p2 = ContractionLeftRule(p1, f)

      val etSeq = extractExpansionSequent(p2, false)

      etSeq.antecedent.count(_.isInstanceOf[WeakQuantifierET]) mustEqual 1
      etSeq.antecedent.count(_.isInstanceOf[AtomET]) mustEqual 1

    }
  }

}

