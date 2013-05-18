/*
 * Tests for the MiniSAT interface.
**/

package at.logic.provers.minisat

import java.io.IOException

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.hol._
import at.logic.calculi.resolution.base._
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.types._
import logicSymbols.ImplicitConverters._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.types.Definitions._

import at.logic.testing.PigeonHolePrinciple

@RunWith(classOf[JUnitRunner])
class MiniSATTest extends SpecificationWithJUnit {
  val box : Set[FClause] = Set()
  def checkForMiniSATOrSkip = (new MiniSAT).solve(box) must not(throwA[IOException]).orSkip

  "MiniSAT" should {
      
    val c = HOLConst(new ConstantStringSymbol("c"), i)
    val d = HOLConst(new ConstantStringSymbol("d"), i)
    val e = HOLConst(new ConstantStringSymbol("e"), i)
    val pc = Atom("P", c::Nil)
    val pd = Atom("P", d::Nil)
    val pe = Atom("P", e::Nil)
      
    "find a model for an atom" in {
      val clause = FClause(Nil, pc::Nil)
      
      (new MiniSAT).solve( (clause::Nil).toSet ) must beLike {
        case Some(model) => ok
        case None => ko
      }
    }
    
    "see that Pc and -Pc is unsat" in {
      val c1 = FClause(Nil, pc::Nil)
      val c2 = FClause(pc::Nil, Nil)
      
      (new MiniSAT).solve( (c1::c2::Nil).toSet ) must beLike {
        case Some(_) => ko
        case None => ok
      }
    }
    
    "see that Pc or -Pc is valid" in {
      (new MiniSAT).isValid( Or(pc, Neg(pc) ) ) must beTrue
    }
    
    "see that Pc is not valid" in {
      (new MiniSAT).isValid( pc ) must beFalse
    }
    
    "return a correct model" in {
      val c1 = FClause(Nil, pc::Nil)
      val c2 = FClause(pc::Nil, pd::Nil)
      val c3 = FClause(pd::pe::Nil, Nil)
      
      (new MiniSAT).solve( (c1::c2::c3::Nil).toSet ) must beLike {
        case Some(model) => if (model.interpret(pe) == false) ok else ko
        case None => ko
      }
      
    }
    
    "deal correctly with the pigeonhole problem" in {
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