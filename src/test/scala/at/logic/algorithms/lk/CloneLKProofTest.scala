package at.logic.algorithms.lk

import at.logic.calculi.lk._
import at.logic.language.fol._
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner


@RunWith(classOf[JUnitRunner])
class CloneLKProofTest extends SpecificationWithJUnit {
  "withMap" should {
    val List(a,b) = List("a","b") map (FOLConst(_))
    val List(x,y) = List("x","y") map (FOLVar(_))
    val p = "P"
    val pay = Atom(p, List(a,y))
    val allxpax = ExVar(x,Atom(p, List(a,x)))
    val ax = Axiom(List(pay), List(pay))
    val i1 = ExistsRightRule(ax, ax.root.succedent(0), allxpax, y)
    val i2 = ExistsLeftRule(i1, i1.root.antecedent(0), allxpax, y)

    "formula occurrences must fit together" in {
      val (_, m) = CloneLKProof.withMap(i2)

      m.forall(p => p._1 =^= p._2) must beTrue
    }
  }
}