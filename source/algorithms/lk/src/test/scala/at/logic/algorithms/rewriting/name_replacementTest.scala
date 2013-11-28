package at.logic.algorithms.rewriting

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
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

/**
 * Test for renaming of constant symbols
 */
@RunWith(classOf[JUnitRunner])
class name_replacementTest extends SpecificationWithJUnit {

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
    //this proof has errors: the factor rule needs a unification
    val List(d1,d2,d3,d4) = List("R(f(a))", "R(f(x))","Q(h(c0))", "Q(x)") map (parse fol)
    val List(x,a,hc) = List("x","a","h(c0)") map (parse folterm)
    val r1 = Substitution[FOLExpression]((x.asInstanceOf[FOLVar], a))
    val r2 = Substitution[FOLExpression]((x.asInstanceOf[FOLVar], hc))
    val q0 = InitialClause(List(d1,d2), List(d3))
    val q1 = Factor(q0, q0.root.negative(1), q0.root.negative(0)::Nil, Substitution[FOLExpression]())
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


    def debug(s:String) = {println("Debug: "+s)}
    val map : NameReplacement.SymbolMap = Map[String, (Int,String)](
      "P" -> (2, "R"),
      "f" -> (1, "h"),
      "g" -> (2, "f"),
      "ladr0" -> (0, "c0")
      )

  "The renaming interface " should {
    "rewrite hol formulas" in {
      val fol1  = parse hol "And P(ladr0:i,f(ladr0:i):i) Or Neg P(a:i,ladr0:i) Q(g(x:o):i)"
      val fol1_ = parse hol "And R(c0:i,h(c0:i):i) Or Neg R(a:i,c0:i) Q(g(x:o):i)"
      fol1_ must beEqualTo( NameReplacement(fol1, map ))
    }

    "rewrite fol formulas" in {
      val fol1  = parse fol "And P(ladr0,f(ladr0)) Or Neg P(a,ladr0) Q(g(x))"
      val fol1_ = parse fol "And R(c0,h(c0)) Or Neg R(a,c0) Q(g(x))"
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

//helpers for parsing
private[rewriting] object parse {
  private class CLIParserFOL(input: String) extends StringReader(input) with SimpleFOLParser
  private class CLIParserHOL(input: String) extends StringReader(input) with SimpleHOLParser

  def fol(string:String) = {
    new CLIParserFOL(string).getTerm.asInstanceOf[FOLFormula]
  }

  def folterm(string:String) = {
    new CLIParserFOL(string).getTerm.asInstanceOf[FOLTerm]
  }

  //this is redundant
  def hol(string:String) = {
    new CLIParserHOL(string) getTerm
  }

  //    def slk(file:String) = {
  //      ParseQMON.parseProofFlat( new InputStreamReader(new FileInputStream( file ) ) )
  //    }
}

