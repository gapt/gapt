package at.logic.algorithms.rewriting

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import org.specs2._
import util.parsing.input.Reader
import at.logic.parsing.readers.StringReader
import at.logic.parsing.language.simple.{SimpleHOLParser, SimpleFOLParser}
import at.logic.language.fol.{FOLExpression, FOLVar, FOLTerm, FOLFormula}
import java.io.{FileInputStream, InputStreamReader}
import at.logic.language.lambda.substitutions.Substitution
import at.logic.calculi.resolution.robinson._
import at.logic.calculi.resolution.base.Clause
import at.logic.calculi.agraphProofs.AGraphProof
import at.logic.utils.ds.acyclicGraphs.{BinaryAGraph, UnaryAGraph, LeafAGraph, AGraph}
import at.logic.language.lambda.typedLambdaCalculus.LambdaExpression
import at.logic.language.lambda.symbols.FreshVariableSymbolFactory
import scala.collection.immutable.HashMap

/**
 * Test for replacment of constant symbols by terms
 */
@RunWith(classOf[JUnitRunner])
class TermReplacementTest extends SpecificationWithJUnit {
  //parse object is in name_replacementTest

  object proof1 {
    val List(c1,c2,c3,c4) = List("P(g(a))", "P(g(x))","Q(f(ladr0))", "Q(x)") map (parse fol)
    val List(x,a,fl) = List("x","a","f(ladr0)") map (parse folterm)
    val s1 = Substitution[FOLExpression]((x.asInstanceOf[FOLVar], a))
    val s2 = Substitution[FOLExpression]((x.asInstanceOf[FOLVar], fl))
    val p1 = InitialClause(List(c1,c1), List(c3))
    val p2 = InitialClause(Nil, List(c2))
    val p3 = InitialClause(List(c4), Nil)
    val p5 = Resolution(p2, p1, p2.root.positive(0), p1.root.negative(1), s1)
    val p6 = Resolution(p5, p3, p5.root.positive(0) ,p3.root.negative(0), s2)
    val p7 = Resolution(p2, p6, p2.root.positive(0), p6.root.negative(0), s1)
  }

  object proof2 {
    val List(d1,d2,d3,d4) = List("R(f(a))", "R(f(x))","Q(h(c0))", "Q(x)") map (parse fol)
    val List(x,a,hc) = List("x","a","h(c0)") map (parse folterm)
    val r1 = Substitution[FOLExpression]((x.asInstanceOf[FOLVar], a))
    val r2 = Substitution[FOLExpression]((x.asInstanceOf[FOLVar], hc))
    val q1 = InitialClause(List(d1,d1), List(d3))
    val q2 = InitialClause(Nil, List(d2))
    val q3 = InitialClause(List(d4), Nil)
    val q5 = Resolution(q2, q1, q2.root.positive(0), q1.root.negative(1), r1)
    val q6 = Resolution(q5, q3, q5.root.positive(0) ,q3.root.negative(0), r2)
    val q7 = Resolution(q2, q6, q2.root.positive(0), q6.root.negative(0), r1)
  }

  object proof3 {
    val List(c1,c2,c3,c4) = List("P(g(a))", "P(g(x))","Q(f(ladr0))", "Q(x)") map (parse fol)
    val List(x,a,fl) = List("x","a","f(ladr0)") map (parse folterm)
    val s1 = Substitution[FOLExpression]((x.asInstanceOf[FOLVar], a))
    val s2 = Substitution[FOLExpression]((x.asInstanceOf[FOLVar], fl))
    val p0 = InitialClause(List(c1,c2), List(c3))
    val p1 = Factor(p0, p0.root.negative(1), p0.root.negative(0)::Nil, Substitution[FOLExpression]())
    val p2 = InitialClause(Nil, List(c2))
    val p3 = InitialClause(List(c4), Nil)
    val p5 = Resolution(p2, p1, p2.root.positive(0), p1.root.negative(0), s1)
    val p6 = Resolution(p5, p3, p5.root.positive(0) ,p3.root.negative(0), s2)
  }

  object proof4 {
    val List(d1,d2,d3,d4) = List("R(f(a))", "R(f(x))","Q(h(c0))", "Q(x)") map (parse fol)
    val List(x,a,hc) = List("x","a","h(c0)") map (parse folterm)
    val r1 = Substitution[FOLExpression]((x.asInstanceOf[FOLVar], a))
    val r2 = Substitution[FOLExpression]((x.asInstanceOf[FOLVar], hc))
    val r3 = Substitution[FOLExpression]()
    val q0 = InitialClause(List(d1,d2), List(d3))
    val q1 = Factor(q0, q0.root.negative(0), q0.root.negative(1)::Nil, r2)
    val q2 = InitialClause(Nil, List(d2))
    val q3 = InitialClause(List(d4), Nil)
    val q5 = Resolution(q2, q1, q2.root.positive(0), q1.root.negative(0), r1)
    val q6 = Resolution(q5, q3, q5.root.positive(0) ,q3.root.negative(0), r2)

  }


  object proof5 {
    val List(c1,c2,c3,c4) = List("P(g(a))", "P(g(x))","P(g(y))", "P(z)") map (parse fol)
    val List(d1,d2,d3,d4) = List("R(f(a))", "R(f(x))","R(f(y))", "R(z)") map (parse fol)
    val List(x,a,y) = List("x","a","y") map (parse folterm)
    /*
    val s1 = Substitution[FOLExpression]((x.asInstanceOf[FOLVar], a))
    val p0 = InitialClause(List(c1,c1), List(c3))
    val p1 = Factor(p0, p0.root.negative(0), p0.root.negative(1)::Nil, s1)
    val p2 = InitialClause(Nil, List(c2))
    val p5 = Resolution(p2, p1, p2.root.positive(0), p1.root.negative(0), s1)
    */
  }

  val emptymap = HashMap[LambdaExpression, LambdaExpression]()

  "Term replacement " should {
    " work on lambda terms " in {
      val List(o1,o2) = List("g(f(g(f),c),f(x,f))","term(term(x),term(a),term(a),term(x))") map (parse.folterm)
      val List(r1,r2) = List("g(f(g(x),c),f(x,x))","term(hihi(x),term(a),term(a),hihi(x))") map (parse.folterm)
      val List(t1,t2,t3,t4) = List("f","x","term(x)","hihi(x)") map (parse.folterm)

      val rt1 = TermReplacement(o1, t1,t2)
      val rt2 = TermReplacement(o2, t3,t4)
      println(rt1)
      println(rt2)
      rt1 must be_==(r1)
      rt2 must be_==(r2)

      val map = emptymap ++ List((t1,t2),(t3,t4))
      rt1 must be_==(TermReplacement(o1,map))
      rt2 must be_==(TermReplacement(o2,map))
    }

    " work on simple proofs " in {
      val List(t1,t2) = List("replacement(x0,y0)", "really(x1)") map parse.folterm
      val map : TermReplacement.SymbolMap = TermReplacement.emptySymbolMap ++ List((proof4.a,t1), (proof4.hc,t2))
      println("Map: "+map)

      println(Formatter.asHumanReadableString(proof4.q6))

      val initial = TermReplacement.rename_resproof(proof4.q0, Set[RobinsonResolutionProof](), map)

      FreshVariableSymbolFactory
      println(initial.root)
      initial.root.occurrences.toList.map(_.formula) must_==( List("R(f(replacement(x0, y0)))", "R(f(x))","Q(really(x1))") map parse.fol  )

      val more = TermReplacement.rename_resproof(proof4.q6, Set[RobinsonResolutionProof](), map)
      println(Formatter.asHumanReadableString(more))

      true must beTrue

    }
  }
}
