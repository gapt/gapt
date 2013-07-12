/*
 * Tests for the MiniSAT interface.
**/

package at.logic.provers.minisat

import java.io.IOException

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language._
import at.logic.language.hol._
import at.logic.calculi.resolution.base._
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.types._
import logicSymbols.ImplicitConverters._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.types.Definitions._

@RunWith(classOf[JUnitRunner])
class MiniSATTest extends SpecificationWithJUnit {
  val box : Set[FClause] = Set()
  def checkForMiniSATOrSkip = (new MiniSAT).solve(box) must not(throwA[IOException]).orSkip

  object PigeonHolePrinciple {
    // The binary relation symbol.
    val rel = ConstantStringSymbol("R")

    def apply( ps: Int, hs: Int ) = {
      assert( ps > 1 )
      fol.Imp( fol.Utils.andN( (1 to ps).map( p =>
              fol.Utils.orN( (1 to hs).map( h => atom(p, h) ).toList ) ).toList ),
            fol.Utils.orN( (1 to hs).map ( h =>
              fol.Utils.orN( (2 to ps).map( p =>
                fol.Utils.orN( ((1 to p - 1)).map( pp =>
                  fol.And(atom(p, h),atom(pp,h))).toList)).toList)).toList))
    }

    def atom( p: Int, h: Int ) = fol.Atom(rel, pigeon(p)::hole(h)::Nil)

    def pigeon(i: Int) = fol.FOLConst(ConstantStringSymbol("p_" + i))

    def hole(i: Int) = fol.FOLConst(ConstantStringSymbol("h_" + i))
  }

  "MiniSAT" should {
      
    val c = HOLConst(new ConstantStringSymbol("c"), i)
    val d = HOLConst(new ConstantStringSymbol("d"), i)
    val e = HOLConst(new ConstantStringSymbol("e"), i)
    val pc = Atom("P", c::Nil)
    val pd = Atom("P", d::Nil)
    val pe = Atom("P", e::Nil)
      
    "find a model for an atom" in {
      (new MiniSAT).solve(box) must not(throwA[IOException]).orSkip

      val clause = FClause(Nil, pc::Nil)
      
      (new MiniSAT).solve( (clause::Nil).toSet ) must beLike {
        case Some(model) => ok
        case None => ko
      }
    }
    
    "see that Pc and -Pc is unsat" in {
      (new MiniSAT).solve(box) must not(throwA[IOException]).orSkip

      val c1 = FClause(Nil, pc::Nil)
      val c2 = FClause(pc::Nil, Nil)
      
      (new MiniSAT).solve( (c1::c2::Nil).toSet ) must beLike {
        case Some(_) => ko
        case None => ok
      }
    }
    
    "see that Pc or -Pc is valid" in {
      (new MiniSAT).solve(box) must not(throwA[IOException]).orSkip

      (new MiniSAT).isValid( Or(pc, Neg(pc) ) ) must beTrue
    }
    
    "see that Pc is not valid" in {
      (new MiniSAT).solve(box) must not(throwA[IOException]).orSkip

      (new MiniSAT).isValid( pc ) must beFalse
    }
    
    "return a correct model" in {
      (new MiniSAT).solve(box) must not(throwA[IOException]).orSkip

      val c1 = FClause(Nil, pc::Nil)
      val c2 = FClause(pc::Nil, pd::Nil)
      val c3 = FClause(pd::pe::Nil, Nil)
      
      (new MiniSAT).solve( (c1::c2::c3::Nil).toSet ) must beLike {
        case Some(model) => if (model.interpret(pe) == false) ok else ko
        case None => ko
      }
      
    }
    
    "deal correctly with the pigeonhole problem" in {
      (new MiniSAT).solve(box) must not(throwA[IOException]).orSkip

      (new MiniSAT).isValid(PigeonHolePrinciple(2,2)) must beFalse
      (new MiniSAT).isValid(PigeonHolePrinciple(3,3)) must beFalse
      (new MiniSAT).isValid(PigeonHolePrinciple(4,4)) must beFalse
      
      (new MiniSAT).isValid(PigeonHolePrinciple(2,1)) must beTrue
      (new MiniSAT).isValid(PigeonHolePrinciple(3,2)) must beTrue
      (new MiniSAT).isValid(PigeonHolePrinciple(4,3)) must beTrue
      (new MiniSAT).isValid(PigeonHolePrinciple(4,1)) must beTrue
    }
  }
}
