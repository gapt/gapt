/* Description: Tests for the base prover
**/

package at.logic.provers.atp

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.fol._
import at.logic.parsing.language.simple.SimpleFOLParser
import at.logic.provers.atp.commands.base.{BranchCommand, Command}
import at.logic.provers.atp.commands.logical.DeterministicAndCommand
import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
import at.logic.calculi.lk.base.FSequent
import at.logic.provers.atp.commands.refinements.simple._
import at.logic.provers.atp.commands.refinements.base._
import at.logic.provers.atp.commands.sequents._
import at.logic.provers.atp.commands.robinson._
import at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
import at.logic.parsing.readers.StringReader
import at.logic.calculi.resolution._
import at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithmFOL

private class MyParser(str: String) extends StringReader(str) with SimpleResolutionParserFOL
private object MyProver extends Prover[Clause]

@RunWith(classOf[JUnitRunner])
class ProverTest extends SpecificationWithJUnit {

  def parse(str:String) : FOLFormula = (new StringReader(str) with SimpleFOLParser getTerm).asInstanceOf[FOLFormula]

  // stream based on macro command that optimize the stack usage
  def stream1a: Stream[Command[Clause]] = Stream.cons(SequentsMacroCommand[Clause](
    SimpleRefinementGetCommand[Clause],
    List(VariantsCommand,ApplyOnAllPolarizedLiteralPairsCommand[Clause], ResolveCommand(FOLUnificationAlgorithm),FactorCommand(FOLUnificationAlgorithm),
      SimpleForwardSubsumptionCommand[Clause](StillmanSubsumptionAlgorithmFOL),
      SimpleBackwardSubsumptionCommand[Clause](StillmanSubsumptionAlgorithmFOL),
      InsertResolventCommand[Clause]),
    RefutationReachedCommand[Clause]), stream1a)
  def streama: Stream[Command[Clause]] = Stream.cons(SetTargetClause(FSequent(List(),List())), Stream.cons(SearchForEmptyClauseCommand[Clause], stream1a))

  // stream based on normal stack usage using configurations normally - may explode stack if branching too fast
  def stream1b:  Stream[Command[Clause]] = Stream.cons(SimpleRefinementGetCommand[Clause],
    Stream.cons(VariantsCommand,
    Stream.cons(BranchCommand[Clause](List(
      Stream(ApplyOnAllPolarizedLiteralPairsCommand[Clause], ResolveCommand(FOLUnificationAlgorithm), FactorCommand(FOLUnificationAlgorithm)),
      Stream(ParamodulationCommand(FOLUnificationAlgorithm)))),
    Stream.cons(SimpleForwardSubsumptionCommand[Clause](StillmanSubsumptionAlgorithmFOL),
    Stream.cons(SimpleBackwardSubsumptionCommand[Clause](StillmanSubsumptionAlgorithmFOL),
    Stream.cons(InsertResolventCommand[Clause],
    Stream.cons(RefutationReachedCommand[Clause], stream1b)))))))
  def streamb: Stream[Command[Clause]] = Stream.cons(SetTargetClause(FSequent(List(),List())), Stream.cons(SearchForEmptyClauseCommand[Clause], stream1b))

  // stream based on "deterministic and command" that allows branching in a sequential way, which can be used in user interfaces as the other commands might
  // ask for an input, put it in the stack and will not necessarily act on it immediately.
  def stream1c: Stream[Command[Clause]] =  Stream.cons(SimpleRefinementGetCommand[Clause],
    Stream.cons(VariantsCommand,
    Stream.cons(DeterministicAndCommand[Clause]((
      List(ApplyOnAllPolarizedLiteralPairsCommand[Clause], ResolveCommand(FOLUnificationAlgorithm), FactorCommand(FOLUnificationAlgorithm)),
      List(ParamodulationCommand(FOLUnificationAlgorithm)))),
    Stream.cons(SimpleForwardSubsumptionCommand[Clause](StillmanSubsumptionAlgorithmFOL),
    Stream.cons(SimpleBackwardSubsumptionCommand[Clause](StillmanSubsumptionAlgorithmFOL),
    Stream.cons(InsertResolventCommand[Clause],
    Stream.cons(RefutationReachedCommand[Clause], stream1c)))))))
  def streamc: Stream[Command[Clause]] = Stream.cons(SetTargetClause(FSequent(List(),List())), Stream.cons(SearchForEmptyClauseCommand[Clause], stream1c))

  def stream1d: Stream[Command[Clause]] =  Stream.cons(SimpleRefinementGetCommand[Clause],
    Stream.cons(VariantsCommand,
    Stream.cons(DeterministicAndCommand[Clause]((
      List(ClauseFactorCommand(FOLUnificationAlgorithm), ApplyOnAllPolarizedLiteralPairsCommand[Clause], ResolveCommand(FOLUnificationAlgorithm)),
      List(ParamodulationCommand(FOLUnificationAlgorithm)))),
    Stream.cons(InsertResolventCommand[Clause],
    Stream.cons(RefutationReachedCommand[Clause], stream1d)))))
  def streamd(f: FSequent): Stream[Command[Clause]] = Stream.cons(SetTargetClause(f), Stream.cons(SearchForEmptyClauseCommand[Clause], stream1d))
  def stream1e: Stream[Command[Clause]] =  Stream.cons(SimpleRefinementGetCommand[Clause],
    Stream.cons(VariantsCommand,
    Stream.cons(ClauseFactorCommand(FOLUnificationAlgorithm),
    Stream.cons(DeterministicAndCommand[Clause]((
      List(ApplyOnAllPolarizedLiteralPairsCommand[Clause], ResolveCommand(FOLUnificationAlgorithm)),
      List(ParamodulationCommand(FOLUnificationAlgorithm)))),
    Stream.cons(SimpleForwardSubsumptionCommand[Clause](StillmanSubsumptionAlgorithmFOL),
    Stream.cons(SimpleBackwardSubsumptionCommand[Clause](StillmanSubsumptionAlgorithmFOL),
    Stream.cons(InsertResolventCommand[Clause],
    Stream.cons(RefutationReachedCommand[Clause], stream1e))))))))
  def streame: Stream[Command[Clause]] = Stream.cons(SetTargetClause(FSequent(List(),List())), Stream.cons(SearchForEmptyClauseCommand[Clause], stream1e))

  def getRefutation(str: String): Boolean = MyProver.refute(Stream.cons(SetClausesCommand(new MyParser(str).getClauseList), streamc)).next must beLike {
      case Some(a) if a.asInstanceOf[ResolutionProof[Clause]].root =^ Clause(List(),List()) => ok
      case _ => ko
    }
   def getRefutationd(str: String, f: FSequent): Boolean = MyProver.refute(Stream.cons(SetClausesCommand(new MyParser(str).getClauseList), streamd(f))).next must beLike {
      case Some(_) => ok
      case _ => ko
    }
   def getRefutatione(str: String): Boolean = MyProver.refute(Stream.cons(SetClausesCommand(new MyParser(str).getClauseList), streame)).next must beLike {
      case Some(a) if a.asInstanceOf[ResolutionProof[Clause]].root =^ Clause(List(),List()) => ok
      case _ => ko
    }

  "Prover" should {
    
    "in case it has only one clause return it if it is the empty clause" in {
      getRefutation(".") must beTrue    
    }
    "in case it has an empty clause set return None" in {
      MyProver.refute(Stream.cons(SetClausesCommand(new MyParser("").getClauseList), streamc)).next must beLike {
        case None => ok
        case _ => ko
      }
    }
    "in case it has only one clause return None if it is not the empty clause" in {
      MyProver.refute(Stream.cons(SetClausesCommand(new MyParser("P(x).").getClauseList), streamc)).next must beLike {
        case None => ok
        case _ => ko
      }
    }
    "refute the following clauses" in {
      "p(a). -p(x) | p(f(x)). -p(f(f(a)))" in {
        getRefutation("P(a). -P(x) | P(f(x)). -P(f(f(a))).") must beTrue
      }
      "requiring factoring" in {
        "p(a). -p(y) | -p(x) | p(f(y)) | p(f(x)). -p(f(f(a)))" in {
          getRefutation("P(a). -P(y) | -P(x) | P(f(y)) | P(f(x)). -P(f(f(a))).") must beTrue
        }
      }
      "requiring factoring with inefficient factoring" in {
        "=(x,x). -=(a,a) | -=(a,a)." in {
          getRefutatione("=(x,x). -=(a,a) | -=(a,a).") must beTrue
        }
      }
      "requiring factoring with inefficient factoring (2)" in {
        "=(x,x). -=(x,x) | -=(x,x)." in {
          getRefutatione("=(x,x). -=(x,x) | -=(x,x).") must beTrue
        }
      }
      "requiring non-terminal factoring" in {
        "P(a). -P(x) | P(f(x)) | P(f(y)). -P(f(f(a))). -P(f(f(b)))." in {
          getRefutation("P(a). -P(x) | P(f(x)) | P(f(y)). -P(f(f(a))). -P(f(f(b))).") must beTrue
        }
      }
     "requiring paramodulation" in {
        "P(a). -P(b). =(a,b)." in {
          getRefutation("P(a). -P(b). =(a,b).") must beTrue
        }
      }
      /*"non-trivial example" in {
        getRefutation("Animal(x) | -Wolf(x). Animal(x) | -Fox(x). Animal(x) | -Bird(x). Animal(x) | -Caterpillar(x). Animal(x) | -Snail(x). Wolf(a_wolf). Fox(a_fox). Bird(a_bird). Caterpillar(a_caterpillar). Snail(a_snail). Grain(a_grain). Plant(x) | -Grain(x). Eats(animal,plant) | Eats(animal,small_animal) | -Animal(animal) | -Plant(plant) | -Animal(small_animal) | -Plant(other_plant) | -Much_smaller(small_animal,animal) | -Eats(small_animal,other_plant). Much_smaller(catapillar,bird) | -Caterpillar(catapillar) | -Bird(bird). Much_smaller(snail,bird) | -Snail(snail) | -Bird(bird). Much_smaller(bird,fox) | -Bird(bird) | -Fox(fox). Much_smaller(fox,wolf) | -Fox(fox) | -Wolf(wolf). -Wolf(wolf) | -Fox(fox) | -Eats(wolf,fox). -Wolf(wolf) | -Grain(grain) | -Eats(wolf,grain). Eats(bird,catapillar) | -Bird(bird) | -Caterpillar(catapillar). -Bird(bird) | -Snail(snail) | -Eats(bird,snail). Plant(caterpillar_food_of(catapillar)) | -Caterpillar(catapillar). Eats(catapillar,caterpillar_food_of(catapillar)) | -Caterpillar(catapillar). Plant(snail_food_of(snail)) | -Snail(snail). Eats(snail,snail_food_of(snail)) | -Snail(snail). -Animal(animal) | -Animal(grain_eater) | -Grain(grain) | -Eats(animal,grain_eater) | -Eats(grain_eater,grain).") must beTrue
      } */
    }
    "obtain the conclusion from premises" in {
      "-P(x) | P(f(x)) from -P(x) | -P(y) | P(f(x)). P(x). " in {
        val var1 = FOLVar("x")
        val fun1 = Function("f", var1::Nil)
        val lit1 = Atom("P",var1::Nil)
        val lit2 = Atom("P",fun1::Nil)
        val init = new MyParser("-P(x) | -P(y) | P(f(x)). P(x).").getClauseList
        val target = FSequent(List(lit1),List(lit2))
        SearchDerivation(init, target) must beLike {
          case Some(_) => ok
          case _ => ko
        }
      }
      "P(f(a)) from -P(x) | -P(y) | P(f(x)) | P(f(y)). P(a)." in {
        val pfa = parse("P(f(a))")
        val init = new MyParser(" -P(x) | -P(y) | P(f(x)) | P(f(y)). P(a).").getClauseList
        val target = FSequent(List(),List(pfa))
        SearchDerivation(init, target) must beLike {
          case Some(_) => ok
          case _ => ko
        }
      }
      "-P(f(a)) from -=(z,z) | -P(x) | -P(y) | P(f(x)) | P(f(y)). -P(f(f(a))). =(x,x)." in {
        val pfa = parse("P(f(a))")
        val init = new MyParser("-=(z,z) | -P(x) | -P(y) | P(f(x)) | P(f(y)). -P(f(f(a))). =(x,x).").getClauseList
        val target = FSequent(List(pfa),List())
        SearchDerivation(init, target) must beLike {
          case Some(_) => ok
          case _ => ko
        }
      }
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
