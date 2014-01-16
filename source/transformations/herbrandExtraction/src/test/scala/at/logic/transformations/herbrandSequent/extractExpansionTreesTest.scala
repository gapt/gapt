package at.logic.transformations.herbrandSequent

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.hol._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.types.Definitions._
import at.logic.transformations.herbrandExtraction._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.calculi.expansionTrees.{StrongQuantifier => StrongQuantifierET, WeakQuantifier => WeakQuantifierET, Atom => AtomET, Imp => ImpET}
import at.logic.calculi.lk.base.LKProof
import at.logic.language.fol.{Function => FOLFunction, FOLConst, FOLVar, Utils}

@RunWith(classOf[JUnitRunner])
class ExtractExpansionTreesTest extends SpecificationWithJUnit {

  def LinearExampleProof(k: Int, n: Int): LKProof = {
    val s = new ConstantStringSymbol("s")
    val p = new ConstantStringSymbol("P")

    val x = FOLVar(VariableStringSymbol("x"))
    val ass = AllVar(x, Imp(Atom(p, x :: Nil), Atom(p, FOLFunction(s, x :: Nil) :: Nil)))
    if (k == n) {
      val a = Atom(p, Utils.numeral(n) :: Nil)
      WeakeningLeftRule(Axiom(a :: Nil, a :: Nil), ass)
    } else {
      val p1 = Atom(p, Utils.numeral(k) :: Nil)
      val p2 = Atom(p, Utils.numeral(k + 1) :: Nil)
      val aux = Imp(p1, p2)
      ContractionLeftRule(ForallLeftRule(ImpLeftRule(Axiom(p1 :: Nil, p1 :: Nil), LinearExampleProof(k + 1, n), p1, p2), aux, ass, Utils.numeral(k)), ass)
    }
  }


  "The expansion tree extraction" should {

    "handle successive contractions " in {
      val etSeq = extractExpansionTrees(LinearExampleProof(0, 2))

      val p = new ConstantStringSymbol("P")
      val x = FOLVar(VariableStringSymbol("x"))
      val s = new ConstantStringSymbol("s")

      val ass = AllVar(x, Imp(Atom(p, x :: Nil), Atom(p, FOLFunction(s, x :: Nil) :: Nil)))

      val equal_permut_1 = etSeq.antecedent equals List(
        AtomET(Atom(p, Utils.numeral(0)::Nil)),
        WeakQuantifierET( ass, List(
          (ImpET( AtomET( Atom(p, Utils.numeral(0)::Nil)), AtomET( Atom(p, Utils.numeral(1)::Nil) ) ), Utils.numeral(0)),
          (ImpET( AtomET( Atom(p, Utils.numeral(1)::Nil)), AtomET( Atom(p, Utils.numeral(2)::Nil) ) ), Utils.numeral(1)))
        )
      )

      val equal_permut_2 = etSeq.antecedent equals List(
        AtomET(Atom(p, Utils.numeral(0)::Nil)),
        WeakQuantifierET( ass, List(
          (ImpET( AtomET( Atom(p, Utils.numeral(1)::Nil)), AtomET( Atom(p, Utils.numeral(2)::Nil) ) ), Utils.numeral(1)),
          (ImpET( AtomET( Atom(p, Utils.numeral(0)::Nil)), AtomET( Atom(p, Utils.numeral(1)::Nil) ) ), Utils.numeral(0)))
        )
      )

      (equal_permut_1 || equal_permut_2) must beTrue

      etSeq.succedent mustEqual( List( AtomET( Atom(p, Utils.numeral(2)::Nil) ) ) )
    }

    "do merge triggering a substitution triggering a merge" in {

      val alpha = HOLVar(VariableStringSymbol("\\alpha"), i)
      val beta = HOLVar(VariableStringSymbol("\\beta"), i)
      val c = HOLConst(ConstantStringSymbol("c"), i)
      val d = HOLConst(ConstantStringSymbol("d"), i)
      val f = ConstantStringSymbol("f")
      val x = HOLVar(VariableStringSymbol("x"), i)
      val y = HOLVar(VariableStringSymbol("y"), i)
      val z = HOLVar(VariableStringSymbol("z"), i)
      val P = new ConstantStringSymbol("P")
      val Q = new ConstantStringSymbol("Q")

      val p0 = Axiom(List(Atom(P, alpha::Nil), Atom(P, beta::Nil)), // P(a), P(b)
                     List(Atom(Q, Function(f, alpha::Nil, i)::c::Nil), Atom(Q, Function(f, beta::Nil, i)::d::Nil))) // Q(f(a), c), Q(f(b), d)
      val p1 = ExistsRightRule(p0, Atom(Q, Function(f, alpha::Nil, i)::c::Nil), ExVar(z, Atom(Q, Function(f, alpha::Nil, i)::z::Nil)), c)
      val p2 = ExistsRightRule(p1, Atom(Q, Function(f, beta::Nil, i)::d::Nil), ExVar(z, Atom(Q, Function(f, beta::Nil, i)::z::Nil)), d)

      val p2_1 = ExistsRightRule(p2, ExVar(z, Atom(Q, Function(f, alpha::Nil, i)::z::Nil)), ExVar(y, ExVar(z, Atom(Q, y::z::Nil))), Function(f, alpha::Nil, i))
      val p2_2 = ExistsRightRule(p2_1, ExVar(z, Atom(Q, Function(f, beta::Nil, i)::z::Nil)), ExVar(y, ExVar(z, Atom(Q, y::z::Nil))), Function(f, beta::Nil, i))

      val p2_3 = ContractionRightRule(p2_2, ExVar(y, ExVar(z, Atom(Q, y::z::Nil))))

      val p3 = ExistsLeftRule(p2_3, Atom(P, alpha::Nil), ExVar(x, Atom(P, x::Nil)), alpha)
      val p4 = ExistsLeftRule(p3, Atom(P, beta::Nil), ExVar(x, Atom(P, x::Nil)), beta)
      val p5 = ContractionLeftRule(p4, ExVar(x, Atom(P, x::Nil)))

      val (ante, succ) = extractExpansionTrees( p5 ).toTuple()

      ante mustEqual( List(StrongQuantifierET( ExVar(x, Atom(P, x::Nil)), alpha, AtomET(Atom(P, alpha::Nil)))) )
      // this assumes that the first variable wins, f(beta) would also be valid
      val f_alpha = Function(f, alpha::Nil, i)
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

      val (ante, succ) = extractExpansionTrees(p4).toTuple()
      ante mustEqual AtomET(BottomC)::Nil
      succ mustEqual AtomET(TopC)::Nil
    }

    "handle multiple formulas in axiom" in {
      val s = new ConstantStringSymbol("s")
      val c = FOLConst(new ConstantStringSymbol("c"))
      val d = FOLConst(new ConstantStringSymbol("d"))
      val x = FOLVar(VariableStringSymbol("x"))
      val p = new ConstantStringSymbol("P")

      val f = AllVar(x, Atom(p, x::Nil))

      val p0_0 = Axiom(Atom(p, c::Nil)::f::Nil, Atom(p, c::Nil)::Nil)

      val p0_1 = Axiom(Atom(p, d::Nil)::Nil, Atom(p, d::Nil)::Nil)
      val p0_2 = ForallLeftRule(p0_1, Atom(p, d::Nil), f, d)

      val p1 = AndRightRule(p0_0, p0_2, Atom(p, c::Nil), Atom(p, d::Nil))
      val p2 = ContractionLeftRule(p1, f)

      val etSeq = extractExpansionTrees(p2)

      etSeq.antecedent.count(_.isInstanceOf[WeakQuantifierET]) mustEqual 1
      etSeq.antecedent.count(_.isInstanceOf[AtomET]) mustEqual 1

    }
  }

}

