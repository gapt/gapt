/* Description: Tests for the base prover
**/

package at.logic.provers.atp

import at.logic.provers.atp.commands.base.{Command}
import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
import at.logic.provers.atp.commands.refinements.simple._
import at.logic.provers.atp.commands.sequents._
import at.logic.provers.atp.commands.robinson._
import org.specs._
import at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
import at.logic.parsing.readers.StringReader
import at.logic.calculi.resolution.base._
import at.logic.calculi.resolution.robinson._

private class MyParser(str: String) extends StringReader(str) with SimpleResolutionParserFOL
private object MyProver extends Prover[ClauseOccurrence]

class ProverTest extends SpecificationWithJUnit {
  def stream1: Stream[Command[ClauseOccurrence]] = Stream.cons(SequentsMacroCommand[ClauseOccurrence](
    SimpleRefinementGetCommand[ClauseOccurrence],
    List(VariantsCommand,ApplyOnAllPolarizedLiteralPairsCommand, ResolveCommand(FOLUnificationAlgorithm),FactorCommand(FOLUnificationAlgorithm),
      IfNotExistCommand[ClauseOccurrence], InsertResolventCommand[ClauseOccurrence]),
    RefutationReachedCommand[ClauseOccurrence]), stream1)
  def stream: Stream[Command[ClauseOccurrence]] = Stream.cons(SetTargetClause(Clause(List(),List())), Stream.cons(SearchForEmptyClauseCommand[ClauseOccurrence], stream1))
  def getRefutation(str: String): Boolean = MyProver.refute(Stream.cons(SetClausesCommand(new MyParser(str).getClauseList), stream)).next must beLike {
      case Some(a) if a.asInstanceOf[ResolutionProof[ClauseOccurrence]].root.getClause setEquals Clause(List(),List()) => true
      case _ => false
    }

  "Prover" should {
    "in case it has only one clause return it if it is the empty clause" in {
      getRefutation(".") must beTrue    
    }
    "in case it has an empty clause set return None" in {
      MyProver.refute(Stream.cons(SetClausesCommand(new MyParser("").getClauseList), stream)).next must beLike {
        case None => true
        case _ => false
      }
    }
    "in case it has only one clause return None if it is not the empty clause" in {
      MyProver.refute(Stream.cons(SetClausesCommand(new MyParser("P(x).").getClauseList), stream)).next must beLike {
        case None => true
        case _ => false
      }
    }
    "refute the following clauses" in {
      "p(a). -p(x) | p(f(x)). -p(f(f(a)))" in {
        getRefutation("P(a). -P(x) | P(f(x)). -P(f(f(a))).") must beTrue
      }
      /*"requiring factoring" in {
        "p(a). -p(y) | -p(x) | p(f(y)) | p(f(x)). -p(f(f(a)))" in {
          getRefutation("P(a). -P(y) | -P(x) | P(f(y)) | P(f(x)). -P(f(f(a))).") must beTrue
        }
      } */
      "requiring non-terminal factoring" in {
        "P(a). -P(x) | P(f(x)) | P(f(y)). -P(f(f(a))). -P(f(f(b)))." in {
          getRefutation("P(a). -P(x) | P(f(x)) | P(f(y)). -P(f(f(a))). -P(f(f(b))).") must beTrue
        }
      }
     /*"requiring paramodulation" in {
        "P(a). -P(b). =(a,b)." in {
          getRefutation("P(a). -P(b). =(a,b).") must beTrue
        }
      }  */
    }
    /*"When there is a refutation the proof should be correct (clauses from the set as initials and using only the rules in a correct way" in {
      "ex1"
    }*/
    // test with a different target clause than the empty
  }
}
  /*
  " Prover with unit refinement" should {
    "refute the following clauses" in {
      "p(a). -p(x) | p(f(x)). -p(f(f(a)))" in {
        MyProver.refute(unitAutoStream("P(a). -P(x) | P(f(x)). -P(f(f(a))).")).head must beLike {
          case a: ResolutionProof[_] if a.root setEquals theEmptyClause().root => true
        }
      }
      // this should not work as it cannot resolve :-P(f(a)), P(f(a)) with P(f(a)), P(f(a)):-
      /*"p(a). -p(x) | -p(x) | p(f(x)) | p(f(x)). -p(f(f(a)))" in {
        MyProver.refute(unitAutoStream("P(a). -P(x) | -P(x) | P(f(x)) | P(f(x)). -P(f(f(a))).")).head must beLike {
          case a: ResolutionProof if a.root.formulaEquivalece(theEmptyClause().root) => true
        }
      }
    }
  }

  import at.logic.utils.ds.PublishingBuffer
  
  def createSubsum(pb: PublishingBuffer[Clause]): at.logic.algorithms.subsumption.managers.SubsumptionManager =
    new at.logic.algorithms.subsumption.managers.SimpleManager(pb.asInstanceOf[PublishingBuffer[at.logic.calculi.lk.base.Sequent]],
                        new at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithm[at.logic.language.fol.FOLExpression] {val matchAlg = at.logic.algorithms.matching.fol.FOLMatchingAlgorithm})

  def autoStream(cl: String, createRef: (PublishingBuffer[Clause] => at.logic.provers.atp.refinements.Refinement[Clause])) = {
    val cls = new MyParser(cl).getClauseList
    AutomatedFOLStream(-1, cls, createRef, createSubsum)
  }
  
  def createSimple(pb: PublishingBuffer[Clause]) = new at.logic.provers.atp.refinements.SimpleRefinement(pb)
  def createUnit(pb: PublishingBuffer[Clause]) = new at.logic.provers.atp.refinements.UnitRefinement(pb)

  def simpleAutoStream(cl: String) = autoStream(cl, createSimple)

  def unitAutoStream(cl: String) = autoStream(cl, createUnit)*/

*/