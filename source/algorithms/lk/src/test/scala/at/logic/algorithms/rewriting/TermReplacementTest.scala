package at.logic.algorithms.rewriting

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import org.specs2._
import at.logic.language.fol._
import at.logic.calculi.resolution.robinson._

/**
 * Test for replacment of constant symbols by terms
 */
@RunWith(classOf[JUnitRunner])
class TermReplacementTest extends SpecificationWithJUnit {
    
  val c1 = Atom("P", Function("g", FOLConst("a")::Nil)::Nil)
  val c2 = Atom("P", Function("g", FOLVar("x")::Nil)::Nil)
  val c3 = Atom("Q", Function("f", FOLConst("ladr0")::Nil)::Nil)
  val c4 = Atom("Q", FOLVar("x")::Nil)
  
  val x = FOLVar("x")
  val a = FOLConst("a")
  val fl = Function("f", FOLConst("ladr0")::Nil)
  
  val d1 = Atom("R", Function("f", FOLConst("a")::Nil)::Nil)
  val d2 = Atom("R", Function("f", FOLVar("x")::Nil)::Nil)
  val d3 = Atom("Q", Function("h", FOLConst("c0")::Nil)::Nil)
  val d4 = Atom("Q", FOLVar("x")::Nil)
  
  val hc = Function("h", FOLConst("c0")::Nil)

  object proof1 {
    val s1 = Substitution(Map(x -> a))
    val s2 = Substitution(Map(x -> fl))
    val p1 = InitialClause(List(c1,c1), List(c3))
    val p2 = InitialClause(Nil, List(c2))
    val p3 = InitialClause(List(c4), Nil)
    val p5 = Resolution(p2, p1, p2.root.positive(0), p1.root.negative(1), s1)
    val p6 = Resolution(p5, p3, p5.root.positive(0) ,p3.root.negative(0), s2)
    val p7 = Resolution(p2, p6, p2.root.positive(0), p6.root.negative(0), s1)
  }

  object proof2 {
    val r1 = Substitution(Map(x -> a))
    val r2 = Substitution(Map(x -> hc))
    val q1 = InitialClause(List(d1,d1), List(d3))
    val q2 = InitialClause(Nil, List(d2))
    val q3 = InitialClause(List(d4), Nil)
    val q5 = Resolution(q2, q1, q2.root.positive(0), q1.root.negative(1), r1)
    val q6 = Resolution(q5, q3, q5.root.positive(0) ,q3.root.negative(0), r2)
    val q7 = Resolution(q2, q6, q2.root.positive(0), q6.root.negative(0), r1)
  }

  object proof3 {
    val s1 = Substitution(Map(x -> a))
    val s2 = Substitution(Map(x -> fl))
    val p0 = InitialClause(List(c1,c2), List(c3))
    val p1 = Factor(p0, p0.root.negative(1), p0.root.negative(0)::Nil, Substitution())
    val p2 = InitialClause(Nil, List(c2))
    val p3 = InitialClause(List(c4), Nil)
    val p5 = Resolution(p2, p1, p2.root.positive(0), p1.root.negative(0), s1)
    val p6 = Resolution(p5, p3, p5.root.positive(0) ,p3.root.negative(0), s2)
  }

  object proof4 {
    val r1 = Substitution(Map(x -> a))
    val r2 = Substitution(Map(x -> hc))
    val r3 = Substitution()
    val q0 = InitialClause(List(d1,d2), List(d3))
    val q1 = Factor(q0, q0.root.negative(0), q0.root.negative(1)::Nil, r2)
    val q2 = InitialClause(Nil, List(d2))
    val q3 = InitialClause(List(d4), Nil)
    val q5 = Resolution(q2, q1, q2.root.positive(0), q1.root.negative(0), r1)
    val q6 = Resolution(q5, q3, q5.root.positive(0) ,q3.root.negative(0), r2)

  }
  
  "Term replacement " should {
    " work on lambda terms " in {
      
      val termx = Function("term", FOLVar("x")::Nil)
      val terma = Function("term", FOLConst("a")::Nil)
      val hihix = Function("hihi", FOLVar("x")::Nil)

      val o1 = Function("g", Function("f", Function("g", FOLConst("f")::Nil)::FOLConst("c")::Nil) :: Function("f", FOLVar("x")::FOLConst("f")::Nil) :: Nil)
      val o2 = Function("term", termx :: terma :: terma :: termx :: Nil)

      val r1 = Function("g", Function("f", Function("g", FOLVar("x")::Nil)::FOLConst("c")::Nil) :: Function("f", FOLVar("x")::FOLVar("x")::Nil) :: Nil)
      val r2 = Function("term", hihix :: terma :: terma :: hihix :: Nil)

      val t1 = FOLConst("f")
      val t2 = FOLVar("x")
      val t3 = Function("term", FOLVar("x")::Nil)
      val t4 = Function("hihi", FOLVar("x")::Nil)

      val rt1 = TermReplacement(o1, t1,t2)
      val rt2 = TermReplacement(o2, t3,t4)
      rt1 must be_==(r1)
      rt2 must be_==(r2)

      val map = Map[FOLExpression, FOLExpression]((t1 -> t2), (t3 -> t4))
      rt1 must be_==(TermReplacement(o1,map))
      rt2 must be_==(TermReplacement(o2,map))
    }

    " work on simple proofs " in {
      
      val t1 = Function("replacement", FOLVar("x0") :: FOLVar("y0") :: Nil)
      val t2 = Function("really", FOLVar("x1") :: Nil)
      
      val map : RenameResproof.SymbolMap = RenameResproof.emptySymbolMap ++ List((a,t1), (hc,t2))

      val initial = RenameResproof.rename_resproof(proof4.q0, Set[RobinsonResolutionProof](), map)

      val r1 = Atom("R", Function("f", t1::Nil)::Nil)
      val r2 = Atom("R", Function("f", FOLVar("x")::Nil)::Nil)
      val r3 = Atom("Q", t2::Nil)

      initial.root.occurrences.toList.map(_.formula) must_== (List(r1, r2, r3))

      val more = RenameResproof.rename_resproof(proof4.q6, Set[RobinsonResolutionProof](), map)

      true must beTrue
    }
  }
}
