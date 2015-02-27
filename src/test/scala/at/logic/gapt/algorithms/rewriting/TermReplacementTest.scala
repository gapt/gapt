package at.logic.gapt.algorithms.rewriting

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import org.specs2._
import at.logic.gapt.language.fol._
import at.logic.gapt.proofs.resolution.robinson._

/**
 * Test for replacment of constant symbols by terms
 */
@RunWith(classOf[JUnitRunner])
class TermReplacementTest extends SpecificationWithJUnit {
    
  val c1 = FOLAtom("P", FOLFunction("g", FOLConst("a")::Nil)::Nil)
  val c2 = FOLAtom("P", FOLFunction("g", FOLVar("x")::Nil)::Nil)
  val c3 = FOLAtom("Q", FOLFunction("f", FOLConst("ladr0")::Nil)::Nil)
  val c4 = FOLAtom("Q", FOLVar("x")::Nil)
  
  val x = FOLVar("x")
  val a = FOLConst("a")
  val fl = FOLFunction("f", FOLConst("ladr0")::Nil)
  
  val d1 = FOLAtom("R", FOLFunction("f", FOLConst("a")::Nil)::Nil)
  val d2 = FOLAtom("R", FOLFunction("f", FOLVar("x")::Nil)::Nil)
  val d3 = FOLAtom("Q", FOLFunction("h", FOLConst("c0")::Nil)::Nil)
  val d4 = FOLAtom("Q", FOLVar("x")::Nil)
  
  val hc = FOLFunction("h", FOLConst("c0")::Nil)

  object proof1 {
    val s1 = FOLSubstitution(Map(x -> a))
    val s2 = FOLSubstitution(Map(x -> fl))
    val p1 = InitialClause(List(c1,c1), List(c3))
    val p2 = InitialClause(Nil, List(c2))
    val p3 = InitialClause(List(c4), Nil)
    val p5 = Resolution(p2, p1, p2.root.positive(0), p1.root.negative(1), s1)
    val p6 = Resolution(p5, p3, p5.root.positive(0) ,p3.root.negative(0), s2)
    val p7 = Resolution(p2, p6, p2.root.positive(0), p6.root.negative(0), s1)
  }

  object proof2 {
    val r1 = FOLSubstitution(Map(x -> a))
    val r2 = FOLSubstitution(Map(x -> hc))
    val q1 = InitialClause(List(d1,d1), List(d3))
    val q2 = InitialClause(Nil, List(d2))
    val q3 = InitialClause(List(d4), Nil)
    val q5 = Resolution(q2, q1, q2.root.positive(0), q1.root.negative(1), r1)
    val q6 = Resolution(q5, q3, q5.root.positive(0) ,q3.root.negative(0), r2)
    val q7 = Resolution(q2, q6, q2.root.positive(0), q6.root.negative(0), r1)
  }

  object proof3 {
    val s1 = FOLSubstitution(Map(x -> a))
    val s2 = FOLSubstitution(Map(x -> fl))
    val p0 = InitialClause(List(c1,c2), List(c3))
    val p1 = Factor(p0, p0.root.negative(1), p0.root.negative(0)::Nil, FOLSubstitution())
    val p2 = InitialClause(Nil, List(c2))
    val p3 = InitialClause(List(c4), Nil)
    val p5 = Resolution(p2, p1, p2.root.positive(0), p1.root.negative(0), s1)
    val p6 = Resolution(p5, p3, p5.root.positive(0) ,p3.root.negative(0), s2)
  }

  object proof4 {
    val r1 = FOLSubstitution(Map(x -> a))
    val r2 = FOLSubstitution(Map(x -> hc))
    val r3 = FOLSubstitution()
    val q0 = InitialClause(List(d1,d2), List(d3))
    val q1 = Factor(q0, q0.root.negative(0), q0.root.negative(1)::Nil, r2)
    val q2 = InitialClause(Nil, List(d2))
    val q3 = InitialClause(List(d4), Nil)
    val q5 = Resolution(q2, q1, q2.root.positive(0), q1.root.negative(0), r1)
    val q6 = Resolution(q5, q3, q5.root.positive(0) ,q3.root.negative(0), r2)

  }
  
  "Term replacement " should {
    " work on lambda terms " in {
      
      val termx = FOLFunction("term", FOLVar("x")::Nil)
      val terma = FOLFunction("term", FOLConst("a")::Nil)
      val hihix = FOLFunction("hihi", FOLVar("x")::Nil)

      val o1 = FOLFunction("g", FOLFunction("f", FOLFunction("g", FOLConst("f")::Nil)::FOLConst("c")::Nil) :: FOLFunction("f", FOLVar("x")::FOLConst("f")::Nil) :: Nil)
      val o2 = FOLFunction("term", termx :: terma :: terma :: termx :: Nil)

      val r1 = FOLFunction("g", FOLFunction("f", FOLFunction("g", FOLVar("x")::Nil)::FOLConst("c")::Nil) :: FOLFunction("f", FOLVar("x")::FOLVar("x")::Nil) :: Nil)
      val r2 = FOLFunction("term", hihix :: terma :: terma :: hihix :: Nil)

      val t1 = FOLConst("f")
      val t2 = FOLVar("x")
      val t3 = FOLFunction("term", FOLVar("x")::Nil)
      val t4 = FOLFunction("hihi", FOLVar("x")::Nil)

      val rt1 = TermReplacement(o1, t1,t2)
      val rt2 = TermReplacement(o2, t3,t4)
      rt1 must be_==(r1)
      rt2 must be_==(r2)

      val map = Map[FOLExpression, FOLExpression]((t1 -> t2), (t3 -> t4))
      rt1 must be_==(TermReplacement(o1,map))
      rt2 must be_==(TermReplacement(o2,map))
    }

    " work on simple proofs " in {
      
      val t1 = FOLFunction("replacement", FOLVar("x0") :: FOLVar("y0") :: Nil)
      val t2 = FOLFunction("really", FOLVar("x1") :: Nil)
      
      val map : RenameResproof.SymbolMap = RenameResproof.emptySymbolMap ++ List((a,t1), (hc,t2))

      val initial = RenameResproof.rename_resproof(proof4.q0, Set[RobinsonResolutionProof](), map)

      val r1 = FOLAtom("R", FOLFunction("f", t1::Nil)::Nil)
      val r2 = FOLAtom("R", FOLFunction("f", FOLVar("x")::Nil)::Nil)
      val r3 = FOLAtom("Q", t2::Nil)

      initial.root.occurrences.toList.map(_.formula) must_== (List(r1, r2, r3))

      val more = RenameResproof.rename_resproof(proof4.q6, Set[RobinsonResolutionProof](), map)

      true must beTrue
    }
  }
}
