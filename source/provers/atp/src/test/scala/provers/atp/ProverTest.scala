/* Description: Tests for the base prover
**/

package at.logic.provers.atp

import org.specs._
import org.specs.runner._
import org.specs.mock.Mockito
import org.mockito.Matchers._  // to use matchers like anyInt()
import at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
import at.logic.parsing.readers.StringReader
import at.logic.calculi.resolution.base._
import refinements.SimpleRefinement
import commands._
import commandsParsers.FOLResolutionCommandsParser

private class MyParser(str: String) extends StringReader(str) with SimpleResolutionParserFOL
private object MyProver extends Prover {
  val ref = new SimpleRefinement{}; val prs = new FOLResolutionCommandsParser{};
  def refinement = ref; def commandsParser = prs
}

class ProverTest extends SpecificationWithJUnit {
  "Prover" should {
    "in case it has only one clause return it if it is the empty clause" in {
      MyProver.refute(AutomatedFOLStream(new MyParser(".").getClauseList)).head must beLike {
        case a: ResolutionProof if a.root.formulaEquivalece(theEmptyClause().root) => true
      }
    }
    "in case it has an empty clause set return None" in {
      MyProver.refute(AutomatedFOLStream(new MyParser("").getClauseList)) must beEqual (Stream.empty)
    }
    "in case it has only one clause return None if it is not the empty clause" in {
      MyProver.refute(AutomatedFOLStream(new MyParser("P(x).").getClauseList)) must beEqual (Stream.empty)
    }
    "refute the following clauses" in {
      "p(a). -p(x) | p(f(x)). -p(f(f(a)))" in {
        MyProver.refute(AutomatedFOLStream(new MyParser("P(a). -P(x) | P(f(x)). -P(f(f(a))).").getClauseList)).head must beLike {
          case a: ResolutionProof if a.root.formulaEquivalece(theEmptyClause().root) => true
        }
      }
    }
    /*"When there is a refutation the proof should be correct (clauses from the set as initials and using only the rules in a correct way" in {
      "ex1"
    }*/
    // test with a different target clause than the empty
  }
}
