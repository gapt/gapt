/*
 * Tests for the prover9 interface.
**/

package at.logic.provers.prover9

import _root_.at.logic.calculi.resolution.base.ResolutionProof
import _root_.at.logic.calculi.resolution.robinson.Clause
import _root_.at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
import _root_.at.logic.parsing.language.simple.SimpleFOLParser
import _root_.at.logic.parsing.readers.StringReader
import _root_.at.logic.provers.atp.commands.base.{SetStreamCommand, PrependCommand}
import _root_.at.logic.provers.atp.commands.sequents.SetTargetClause
import _root_.at.logic.provers.atp.Prover
import commands.Prover9InitCommand
import org.specs._
import org.specs.runner._
import org.specs.mock.Mockito
import org.mockito.Matchers._
import java.io.IOException

import at.logic.calculi.occurrences.factory
private class MyParser(str: String) extends StringReader(str) with SimpleResolutionParserFOL

// to use matchers like anyInt()
import at.logic.language.fol._
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.lk.base.types.FSequent

class Prover9Test extends SpecificationWithJUnit {
  def parse(str:String) : FOLFormula = (new StringReader(str) with SimpleFOLParser getTerm).asInstanceOf[FOLFormula]

  val box = List()
  def checkForProver9OrSkip = Prover9.refute(box) must not(throwA[IOException]).orSkip

  implicit def fo2occ(f:FOLFormula) = factory.createFormulaOccurrence(f, Nil)

  private object MyProver extends Prover[Clause]

  def getRefutation(ls: Iterable[FSequent]): Boolean = MyProver.refute(Stream(SetTargetClause((List(),List())), Prover9InitCommand(ls), SetStreamCommand())).next must beLike {
      case Some(a) if a.asInstanceOf[ResolutionProof[Clause]].root syntacticMultisetEquals (List(),List()) => true
      case _ => false
  }

  def getRefutation2(ls: Iterable[FSequent]) = MyProver.refute(Stream(SetTargetClause((List(),List())), Prover9InitCommand(ls), SetStreamCommand())).next

  "Prover9 within ATP" should {
    "prove (with para) SKKx = Ix : { :- f(a,x) = x; :- f(f(f(b,x),y),z) = f(f(x,z), f(y,z)); :- f(f(c,x),y) = x; f(f(f(b,c),c),x) = f(a,x) :- }" in {

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
    }
    /*"prove a non-trivial example" in {
      getRefutation(new MyParser("Animal(x) | -Wolf(x). Animal(x) | -Fox(x). Animal(x) | -Bird(x). Animal(x) | -Caterpillar(x). Animal(x) | -Snail(x). Wolf(a_wolf). Fox(a_fox). Bird(a_bird). Caterpillar(a_caterpillar). Snail(a_snail). Grain(a_grain). Plant(x) | -Grain(x). Eats(x_animal,x_plant) | Eats(x_animal,x_small_animal) | -Animal(x_animal) | -Plant(x_plant) | -Animal(x_small_animal) | -Plant(x_other_plant) | -Much_smaller(x_small_animal,x_animal) | -Eats(x_small_animal,x_other_plant). Much_smaller(x_catapillar,x_bird) | -Caterpillar(x_catapillar) | -Bird(x_bird). Much_smaller(x_snail,x_bird) | -Snail(x_snail) | -Bird(x_bird). Much_smaller(x_bird,x_fox) | -Bird(x_bird) | -Fox(x_fox). Much_smaller(x_fox,x_wolf) | -Fox(x_fox) | -Wolf(x_wolf). -Wolf(x_wolf) | -Fox(x_fox) | -Eats(x_wolf,x_fox). -Wolf(x_wolf) | -Grain(x_grain) | -Eats(x_wolf,x_grain). Eats(x_bird,x_catapillar) | -Bird(x_bird) | -Caterpillar(x_catapillar). -Bird(x_bird) | -Snail(x_snail) | -Eats(x_bird,x_snail). Plant(caterpillar_food_of(x_catapillar)) | -Caterpillar(x_catapillar). Eats(x_catapillar,caterpillar_food_of(x_catapillar)) | -Caterpillar(x_catapillar). Plant(snail_food_of(x_snail)) | -Snail(x_snail). Eats(x_snail,snail_food_of(x_snail)) | -Snail(x_snail). -Animal(x_animal) | -Animal(x_grain_eater) | -Grain(x_grain) | -Eats(x_animal,x_grain_eater) | -Eats(x_grain_eater,x_grain).").getClauseList) must beTrue
    } */
  }

  "The Prover9 interface" should {
    "refute { :- P; P :- }" in {
      //checks, if the execution of prover9 works, o.w. skip test
      Prover9.refute(box ) must not(throwA[IOException]).orSkip

      val p = Atom(new ConstantStringSymbol("P"), Nil)
      val s1 = (Nil, p::Nil)
      val s2 = (p::Nil, Nil)
      val result : Boolean = Prover9.refute( s1::s2::Nil )
      result must beEqual( true )
    }
  }

  "The Prover9 interface" should {
    "prove SKKx = Ix : { :- f(a,x) = x; :- f(f(f(b,x),y),z) = f(f(x,z), f(y,z)); :- f(f(c,x),y) = x; f(f(f(b,c),c),x) = f(a,x) :- }" in {
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
      val result : Boolean = Prover9.refute( List(s1,s2,s3,t1) )
      result must beEqual( true )
    }
  }

  "The Prover9 interface" should {
    "not refute { :- P; Q :- }" in {
      //checks, if the execution of prover9 works, o.w. skip test
      Prover9.refute(box ) must not(throwA[IOException]).orSkip

      val s1 = (Nil, List(parse("P")))
      val t1 = (List(parse("Q")),Nil)
      val result : Boolean = Prover9.refute( List(s1,t1) )
      result must beEqual( false )
    }
  }

}
