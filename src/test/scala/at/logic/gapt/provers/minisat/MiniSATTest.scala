/*
 * Tests for the MiniSAT interface.
**/

package at.logic.gapt.provers.minisat

import java.io.IOException

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.gapt.language.fol._
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.language.lambda.types._
import at.logic.gapt.proofs.lk.base.FSequent

@RunWith(classOf[JUnitRunner])
class MiniSATTest extends SpecificationWithJUnit {
  val box : Set[FClause] = Set()

  args(skipAll = !(new MiniSATProver).isInstalled())

  object PigeonHolePrinciple {
    // The binary relation symbol.
    val rel = "R"

    def apply( ps: Int, hs: Int ) = {
      assert( ps > 1 )
      FOLImp( FOLAnd( (1 to ps).map( p =>
              FOLOr( (1 to hs).map( h => atom(p, h) ).toList ) ).toList ),
            FOLOr( (1 to hs).map ( h =>
              FOLOr( (2 to ps).map( p =>
                FOLOr( ((1 to p - 1)).map( pp =>
                  FOLAnd(atom(p, h),atom(pp,h))).toList)).toList)).toList))
    }

    def atom( p: Int, h: Int ) = FOLAtom(rel, pigeon(p)::hole(h)::Nil)

    def pigeon(i: Int) = FOLConst("p_" + i)

    def hole(i: Int) = FOLConst("h_" + i)
  }

  "MiniSAT" should {
      
    val c = FOLConst("c")
    val d = FOLConst("d")
    val e = FOLConst("e")
    val pc = FOLAtom("P", c::Nil)
    val pd = FOLAtom("P", d::Nil)
    val pe = FOLAtom("P", e::Nil)
      
    "find a model for an atom" in {
      val clause = FClause(Nil, pc::Nil)
     
      (new MiniSAT).solve( (clause::Nil) ) must beLike {
        case Some(model) => ok
        case None => ko
      }
    }
    
    "see that Pc and -Pc is unsat" in {
      val c1 = FClause(Nil, pc::Nil)
      val c2 = FClause(pc::Nil, Nil)
      
      (new MiniSAT).solve( (c1::c2::Nil) ) must beLike {
        case Some(_) => ko
        case None => ok
      }
    }
    
    "see that Pc or -Pc is valid" in {
      (new MiniSAT).isValid( FOLOr(pc, FOLNeg(pc) ) ) must beTrue
      (new MiniSATProver).isValid( new FSequent( Nil, FOLOr(pc, FOLNeg(pc) )::Nil) ) must beTrue
    }
    
    "see that Pc is not valid" in {
      (new MiniSAT).isValid( pc ) must beFalse
    }
    
    "return a correct model" in {
      val c1 = FClause(Nil, pc::Nil)
      val c2 = FClause(pc::Nil, pd::Nil)
      val c3 = FClause(pd::pe::Nil, Nil)
      
      (new MiniSAT).solve( (c1::c2::c3::Nil) ) must beLike {
        case Some(model) => if (model.interpret(pe) == false) ok else ko
        case None => ko
      }
      
    }
    
    "deal correctly with the pigeonhole problem" in {
      val fparams = List((2,2),(3,3),(4,4))
      val tparams = List((2,1),(3,2),(4,3),(4,1))
      def problem(pair: (Int,Int)) = (new MiniSAT).isValid(PigeonHolePrinciple(pair._1,pair._2))

      fparams.map(problem) must_== fparams.map(x => false)
      tparams.map(problem) must_== tparams.map(x => true)
    }
  }
}
