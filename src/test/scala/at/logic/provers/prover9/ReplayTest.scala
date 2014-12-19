/*
 * Tests for the prover9 interface.
**/

package at.logic.provers.prover9

import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.occurrences.factory
import at.logic.calculi.resolution.Clause
import at.logic.calculi.resolution.ResolutionProof
import at.logic.calculi.resolution.robinson.{Formatter, RobinsonResolutionProof}
import at.logic.language.fol._
import at.logic.language.lambda.symbols._
import at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
import at.logic.parsing.language.simple.SimpleFOLParser
import at.logic.parsing.language.tptp.TPTPFOLExporter
import at.logic.parsing.readers.StringReader
import at.logic.provers.atp.Prover
import at.logic.provers.atp.commands.base.{SetStreamCommand, PrependCommand}
import at.logic.provers.atp.commands.sequents.SetTargetClause
import at.logic.provers.prover9.commands.Prover9InitCommand
import java.io.File.separator
import java.io.IOException

import org.junit.runner.RunWith
import org.mockito.Matchers._
import org.specs2.mock.Mockito
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner
import at.logic.parsing.language.prover9.Prover9TermParser.parseFormula
import at.logic.provers.prover9.commands.Prover9InitCommand
import scala.Some
import at.logic.provers.atp.commands.sequents.SetTargetClause
import at.logic.provers.atp.commands.base.SetStreamCommand

@RunWith(classOf[JUnitRunner])
class ReplayTest extends SpecificationWithJUnit {
  def parse(str:String) : FOLFormula = (new StringReader(str) with SimpleFOLParser getTerm).asInstanceOf[FOLFormula]

  val box = List()
  def checkForProver9OrSkip = Prover9.refute(box) must not(throwA[IOException]).orSkip

  implicit def fo2occ(f:FOLFormula) = factory.createFormulaOccurrence(f, Nil)

  private object MyProver extends Prover[Clause]

  def getRefutation(ls: Iterable[FSequent]): Boolean = MyProver.refute(Stream(SetTargetClause(FSequent(List(),List())), Prover9InitCommand(ls), SetStreamCommand())).next must beLike {
      case Some(a) if a.asInstanceOf[ResolutionProof[Clause]].root syntacticMultisetEquals (FSequent(List(),List())) => ok
      case _ => ko
  }

  def getRefutation2(ls: Iterable[FSequent]) = MyProver.refute(Stream(SetTargetClause(FSequent(List(),List())), Prover9InitCommand(ls), SetStreamCommand())).next


  "replay" should {
    /*"prove (with para) SKKx = Ix : { :- f(a,x) = x; :- f(f(f(b,x),y),z) = f(f(x,z), f(y,z)); :- f(f(c,x),y) = x; f(f(f(b,c),c),x) = f(a,x) :- }" in {

      //checks, if the execution of prover9 works, o.w. skip test
      Prover9.refute(box ) must not(throwA[IOException]).orSkip


      val i = parse("=(f(a,x),x)")
      val s = parse("=(f(f(f(b,x),y),z), f(f(x,z), f(y,z)))")
      val k = parse("=(f(f(c,x),y), x)")
      val skk_i = parse("=(f(f(f(b,c),c),x), f(a,x))")

      val s1 = (Nil, List(i))
      val s2 = (Nil, List(k))
      val s3 = (Nil, List(s))
      val t1 = (List(skk_i),Nil)
      getRefutation(List(s1,s2,s3,t1)) must beTrue
    }

    "prove 0) :- p(a) , (1) p(x) :- p(f(x)) , (2) p(f(f(a))) :- " in {
      val pa = parse("P(a)")
      val px = parse("P(x)")
      val pfx = parse("P(f(x))")
      val pffa = parse("P(f(f(a)))")
      val s1 = (Nil, List(pa))
      val s2 = (List(px),List(pfx))
      val s3 = (List(pffa),Nil)
      getRefutation(List(s1,s2,s3)) must beTrue
    }

    "prove 0) :- p(a) , (1) p(x), p(y) :- p(f(x)) , (2) p(f(f(a))) :- " in {
      val pa = parse("P(a)")
      val px = parse("P(x)")
      val py = parse("P(y)")
      val pfx = parse("P(f(x))")
      val pffa = parse("P(f(f(a)))")
      val s1 = (Nil, List(pa))
      val s2 = (List(px,py),List(pfx))
      val s3 = (List(pffa),Nil)
      getRefutation(List(s1,s2,s3)) must beTrue
    }

    "prove (with factor and copy/merge) 0) :- p(a) , (1) p(x), p(y) :- p(f(x)), p(f(y)) , (2) p(f(f(a))) :- " in {
      val pa = parse("P(a)")
      val px = parse("P(x)")
      val py = parse("P(y)")
      val pfx = parse("P(f(x))")
      val pfy = parse("P(f(y))")
      val pffa = parse("P(f(f(a)))")
      val s1 = (Nil, List(pa))
      val s2 = (List(px,py),List(pfx,pfy))
      val s3 = (List(pffa),Nil)
      getRefutation(List(s1,s2,s3)) must beTrue
    }
    "prove (with xx - 1) 0) :- p(a) , (1) z = z, p(x), p(y) :- p(f(x)), p(f(y)) , (2) p(f(f(a))) :- " in {
      val pa = parse("P(a)")
      val px = parse("P(x)")
      val py = parse("P(y)")
      val zz = parse("=(z,z)")
      val pfx = parse("P(f(x))")
      val pfy = parse("P(f(y))")
      val pffa = parse("P(f(f(a)))")
      val s1 = (Nil, List(pa))
      val s2 = (List(zz,px,py),List(pfx,pfy))
      val s3 = (List(pffa),Nil)
      getRefutation(List(s1,s2,s3)) must beTrue
    }
    "prove (with xx - 2) P(f(a)). -=(z,z) | -P(x) | -P(y) | P(f(x)) | P(f(y)). -P(f(f(a)))." in {
      val pfa = parse("P(f(a))")
      val px = parse("P(x)")
      val py = parse("P(y)")
      val zz = parse("=(z,z)")
      val pfx = parse("P(f(x))")
      val pfy = parse("P(f(y))")
      val pffa = parse("P(f(f(a)))")
      val s1 = (Nil, List(pfa))
      val s2 = (List(zz,px,py),List(pfx,pfy))
      val s3 = (List(pffa),Nil)
      (getRefutation2(List(s1,s2,s3)) match {
        case Some(a) if a.asInstanceOf[ResolutionProof[Clause]].toTreeProof.root syntacticMultisetEquals (List(),List()) => true
        case _ => false
      }) must beTrue
    } */

    "work on the tape-in clause set" in {
      val formulas = List(
        "f(X+Y)=0",
        "f(Y+X)=1",
        "f(X + Z0) = 0",
        "f(((X + Z0) + 1) + Z1) = 0",
        "f(X + Z0) = 1",
        "f(((X + Z0) + 1) + Z1) = 1"
      ).map(parseFormula)

      val c1 = FSequent(Nil, List(formulas(0), formulas(1)))
      val c2 = FSequent(List(formulas(2), formulas(3)),Nil)
      val c3 = FSequent(List(formulas(4), formulas(5)),Nil)

      val ls = List(c1,c2,c3)

      val prover = new Prover[Clause] {}

      prover.refute(Stream(
        SetTargetClause(FSequent(List(),List())),
        Prover9InitCommand(ls),
        SetStreamCommand()
      )).next must beLike {
        case Some(a) if a.asInstanceOf[ResolutionProof[Clause]].root syntacticMultisetEquals (FSequent(List(),List())) =>
          ok
        case _ =>
          ko
      }
    }



    "prove (with xx - 3) -=(a,a) | -=(a,a)." in {

      //checks, if the execution of prover9 works (used by getRefutation2), o.w. skip test
      Prover9.refute(box ) must not(throwA[IOException]).orSkip

      val eaa = parse("=(a,a)")
      val s = FSequent(List(eaa,eaa),Nil)
      (getRefutation2(List(s)) match {
        case Some(a) if a.asInstanceOf[ResolutionProof[Clause]].root.toFSequent multiSetEquals  (FSequent(List(),List())) => true
        case _ => false
      }) must beTrue
    }

     "prove an example from the automated deduction exercises" in {
       skipped("never worked")
       Prover9.refute(box ) must not(throwA[IOException]).orSkip

      /* loops at derivation of clause 7:
        <clause id="7">
          <literal>
          ladr3(ladr2,A) = ladr3(B,ladr3(B,A))
          </literal>
          <justification jstring="[para(4(a,1),2(a,1,1))].">
          <j1 parents="4 2" rule="para"></j1>
          </justification>
        </clause>
       */

      //println("=======AD Example: =======")
      val assoc = parse("=(*(x,*(y,z)), *(*(x,y),z) )")
      val neutr = parse("=(*(x,e), x)")
      val idem = parse("=(*(x,x), e)")
      val comm = parse("=(*(x,y), *(y,x))")
      val ncomm = parse("=(*(c1,c2), *(c2,c1))")
      val s1 = FSequent(Nil,List(assoc))
      val s2 = FSequent(Nil,List(neutr))
      val s3 = FSequent(Nil,List(idem))
      val s4 = FSequent(List(ncomm), Nil)
      (getRefutation2(List(s1,s2,s3,s4)) match {
        case Some(a) if a.asInstanceOf[RobinsonResolutionProof].root.toFSequent multiSetEquals  (FSequent(List(),List())) =>
          //println(Formatter.asHumanReadableString(a)   )
          //println("======= GraphViz output: =======\n" + Formatter.asGraphViz(a)   )
          true
        case _ => false
      }) must beTrue
    }

    "refute { :- P; P :- }" in {
      //checks, if the execution of prover9 works, o.w. skip test
      Prover9.refute(box ) must not(throwA[IOException]).orSkip

      val p = Atom("P", Nil)
      val s1 = FSequent(Nil, p::Nil)
      val s2 = FSequent(p::Nil, Nil)
      val result : Option[RobinsonResolutionProof] = Prover9.refute( s1::s2::Nil )
      result match {
        case Some(proof) =>
          //println(Formatter.asHumanReadableString(proof))
          true must beEqualTo(true)
        case None => "" must beEqualTo( "Refutation failed!" )
      }

    }

    "find a refutation for a simple clause set " in {
      //checks, if the execution of prover9 works, o.w. skip test
      Prover9.refute(box ) must not(throwA[IOException]).orSkip
      //println("==== SIMPLE EXAMPLE ====")
      val f_eq_g = parse("=(f(x),g(x))")
      val px = parse("P(x)")
      val pfx = parse("P(f(x))")
      val pa = parse("P(a)")
      val goal = parse("P(g(a))")

      val s1 = FSequent(Nil, List(f_eq_g))
      val s2 = FSequent(List(px), List(pfx))
      val s3 = FSequent(Nil, List(pa))
      val t1 = FSequent(List(goal),Nil)
      //println(TPTPFOLExporter.tptp_problem(List(s1,s2,s3,t1)))
      //println()
      val Some(result) = getRefutation2( List(s1,s2,s3,t1) )
      //println(result)

      //println(Formatter.asTex(result))

      true must beEqualTo( true )
    }
  }

}
