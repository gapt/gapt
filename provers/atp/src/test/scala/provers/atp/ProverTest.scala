/* Description: Tests for the base prover
**/

package at.logic.provers.atp

import org.specs._
import org.specs.runner._
import org.specs.mock.Mockito
import org.mockito.Matchers._  // to use matchers like anyInt()
import at.logic.parsing.calculi.simple.SimpleResolutionParser
import at.logic.parsing.readers.StringReader
import at.logic.calculi.resolution.base._
import refinements.SimpleRefinement
import commands._
import commandsParsers.FOLResolutionCommandsParser

private class MyParser(str: String) extends StringReader(str) with SimpleResolutionParser
private object MyProver extends Prover {val ref = new SimpleRefinement{}; val prs = new FOLResolutionCommandsParser{};
                                      def refinement = ref; def commandsParser = prs}

class ProverTest extends SpecificationWithJUnit {
  "Prover" should {
    "in case it has only one clause return it if it is the empty clause" in {
      MyProver.refute(AutomatedFOLStream(new MyParser(".").getClauseList)).head must beEqual (theEmptyClause())
    }
    "in case it has an empty clause set return None" in {
      MyProver.refute(AutomatedFOLStream(new MyParser("").getClauseList)) must beEqual (Stream.empty)
    }
    /*"in case it has only one clause return None if it is not the empty clause" in {
      new Prover{}.refute(AutomatedFOLStream(new MyParser("P(x:i).").getClauseList)) must beEqual (Stream())
    }
    "When there is a refutation the proof should be correct (clauses from the set as initials and using only the rules in a correct way" in {
      "ex1"
    }*/
    // test with a different target clause than the empty
  }
}
