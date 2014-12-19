package at.logic.algorithms.rewriting

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import at.logic.language.fol._
import at.logic.language.hol.{HOLConst, HOLVar, Atom => HOLAtom, Function => HOLFunction, And => HOLAnd, Or => HOLOr, Neg => HOLNeg}
import at.logic.language.lambda.types._
import at.logic.calculi.resolution.robinson._
import at.logic.calculi.resolution._
import at.logic.utils.ds.acyclicGraphs.{BinaryAGraph, UnaryAGraph, LeafAGraph, AGraph}

/**
 * Test for renaming of constant symbols
 */
@RunWith(classOf[JUnitRunner])
class name_replacementTest extends SpecificationWithJUnit {

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
    //this proof has errors: the factor rule needs a unification
    val r1 = Substitution(Map(x -> a))
    val r2 = Substitution(Map(x -> hc))
    val q0 = InitialClause(List(d1,d2), List(d3))
    val q1 = Factor(q0, q0.root.negative(1), q0.root.negative(0)::Nil, Substitution())
    val q2 = InitialClause(Nil, List(d2))
    val q3 = InitialClause(List(d4), Nil)
    val q5 = Resolution(q2, q1, q2.root.positive(0), q1.root.negative(0), r1)
    val q6 = Resolution(q5, q3, q5.root.positive(0) ,q3.root.negative(0), r2)

  }

  def checkClause(c: Clause, d:Clause) = c.toFSequent multiSetEquals(d.toFSequent)
  def checkTree(r : AGraph[Clause], o : AGraph[Clause]) : Option[(AGraph[Clause], AGraph[Clause])] = {
    val pair : (AGraph[Clause], AGraph[Clause]) = (r,o)
    pair match {
      case (LeafAGraph(c), LeafAGraph(d)) =>
        if (checkClause(c.asInstanceOf[Clause],d.asInstanceOf[Clause])) None else Some((r,o))
      case (UnaryAGraph(c,p), UnaryAGraph(d,q)) =>
        checkTree(p.asInstanceOf[AGraph[Clause]],q.asInstanceOf[AGraph[Clause]]) match {
          case None =>
            if (checkClause(c.asInstanceOf[Clause],d.asInstanceOf[Clause])) None else Some((r,o))
          case e@Some(_) => e
        }
      case (BinaryAGraph(c,p1,p2), BinaryAGraph(d,q1,q2)) =>
        checkTree(p1.asInstanceOf[AGraph[Clause]],q1.asInstanceOf[AGraph[Clause]]) match {
          case None =>
            checkTree(p2.asInstanceOf[AGraph[Clause]],q2.asInstanceOf[AGraph[Clause]]) match {
              case None =>
                if (checkClause(c.asInstanceOf[Clause],d.asInstanceOf[Clause])) None else Some((r,o))
              case Some(e) => Some(e)
            }
          case Some(e) => Some(e)
        }
      case _ => Some((r,o))
    }}


  val map : NameReplacement.SymbolMap = Map[String, (Int,String)](
    "P" -> (2, "R"),
    "f" -> (1, "h"),
    "g" -> (2, "f"),
    "ladr0" -> (0, "c0")
  )

  "The renaming interface " should {
    "rewrite fol formulas" in {
      val p_ladr_fladr = Atom("P", FOLConst("ladr0")::Function("f", FOLConst("ladr0")::Nil)::Nil)
      val p_a_ladr = Atom("P", FOLConst("a")::FOLConst("ladr0")::Nil)
      val q_gx = Atom("Q", Function("g", FOLVar("x")::Nil)::Nil)

      val fol1 = And(p_ladr_fladr, Or(Neg(p_a_ladr), q_gx))

      val r_c_hc = Atom("R", FOLConst("c0")::Function("h", FOLConst("c0")::Nil)::Nil)
      val r_a_c = Atom("R", FOLConst("a")::FOLConst("c0")::Nil)

      val fol1_ = And(r_c_hc, Or(Neg(r_a_c), q_gx))

      fol1_ must beEqualTo( NameReplacement(fol1, map ))
    }

    "rewrite hol formulas" in {
      val P = HOLConst("P", Ti -> (Ti -> To))
      val Q = HOLConst("Q", Ti -> To)
      val R = HOLConst("R", Ti -> (Ti -> To))
      val f = HOLConst("f", Ti -> Ti)
      val g = HOLConst("g", Ti -> Ti)
      val h = HOLConst("h", Ti -> Ti)

      val ladr = HOLConst("ladr0", Ti)
      val c0 = HOLConst("c0", Ti)

      val p_ladr_fladr = HOLAtom(P, ladr::HOLFunction(f, ladr::Nil)::Nil)
      val p_a_ladr = HOLAtom(P, HOLConst("a", Ti)::ladr::Nil)
      val q_gx = HOLAtom(Q, HOLFunction(g, HOLVar("x", Ti)::Nil)::Nil)

      val fol1 = HOLAnd(p_ladr_fladr, HOLOr(HOLNeg(p_a_ladr), q_gx))

      val r_c_hc = HOLAtom(R, c0::HOLFunction(h, c0::Nil)::Nil)
      val r_a_c = HOLAtom(R, HOLConst("a", Ti)::c0::Nil)

      val fol1_ = HOLAnd(r_c_hc, HOLOr(HOLNeg(r_a_c), q_gx))

      fol1_ must beEqualTo( NameReplacement(fol1, map ))
    }

    "rewrite of resolution proofs must work" in {
      //      println(proof1.p7)
      //      println(proof2.q7)
      val map : NameReplacement.SymbolMap = Map[String, (Int,String)](
        "P" -> (1, "R"),
        "f" -> (1, "h"),
        "g" -> (1, "f"),
        "ladr0" -> (0, "c0")
      )

      val (_,proof) = NameReplacement.rename_resproof(proof1.p7, map)
      //println
      //proof4.q0.root.negative map println
      //println
      //proof4.q1.root.negative map println
      //println
      //(proof4.q1.root.negative diff proof4.q0.root.negative) map println
      //println

      //def find_lost_ancestors()

      //proof4.q1 match { case Factor(c,p,aux,s) => aux map println}

      checkTree(proof, proof2.q7) must beEmpty

      val (_,fproof) = NameReplacement.rename_resproof(proof3.p6, map)
      //fproof.nodes map println
      checkTree(fproof, proof4.q6) must beEmpty
    }
  }
}
