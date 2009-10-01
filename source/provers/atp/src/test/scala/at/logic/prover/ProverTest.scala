/* Description: Tests for the base prover
**/

import org.specs._
import org.specs.runner._
import org.specs.mock.Mockito
import org.mockito.Matchers._  // to use matchers like anyInt()
import at.logic.prover.Prover
import at.logic.parsing.calculus._
import at.logic.parsing.language.prover9._
import at.logic.parsing.readers._
import at.logic.parsing.calculus.prover9._
import at.logic.syntax.calculus.resolution._
import at.logic.syntax.language.fol._

/* we should use a string sequent parser in order to easily generate examples
object RefutableExamples {
  def ex1 = TermBuilder.build("-f(x) | f(f(x))")
}
*/

private class MyParser(str: String) extends StringReader(str) with FOLProver9TermParser with Prover9SequentsParser[Clause] with ClausesCreator

class ProverTest extends Specification with JUnit { 
  "Prover" should {
    /*"in case it has only one clause return it if it is the empty clause" in {
      new Prover().refute(new MyParser(".")) must beLike {case Some((InitialRule(Clause(Nil,Nil)), _)) => true}
    }
    "in case it has an empty clause set return None" in {
      new Prover().refute(new MyParser("")) must beEqual (None)
    }
    "in case it has only one clause return None if it is not the empty clause" in {
      new Prover().refute(new MyParser("P(x)")) must beEqual (None)
    }
    "When there is a refutation the proof should be correct (clauses from the set as initials and using only the rules in a correct way" in {
      "ex1"
    }*/
  }
}
