package at.logic.provers.atp.commands

/**
 * this file contains command for a guided search using ids for clauses,as for example when parsing the output of theorem provers and using the rules from there
 */
package replay {

import _root_.at.logic.algorithms.matching.fol.FOLMatchingAlgorithm
import _root_.at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithm
import _root_.at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
import _root_.at.logic.calculi.resolution.base.ResolutionProof
import _root_.at.logic.calculi.resolution.robinson.{RobinsonResolutionProof}
import at.logic.calculi.resolution.base.Clause
import _root_.at.logic.language.hol.HOLFormula
import _root_.at.logic.provers.atp.commands.sequents._
import at.logic.calculi.lk.base.types.FSequent
import _root_.at.logic.provers.atp.Definitions._
import at.logic.calculi.lk.base.{Sequent, FSequent}
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.calculi.resolution.robinson.InitialClause._
import at.logic.language.fol.{FOLVar, FOLExpression, FOLFormula}
import at.logic.language.lambda.typedLambdaCalculus.Var
import at.logic.provers.atp.Prover
import at.logic.utils.ds.PublishingBuffer
import refinements.simple.SimpleRefinementGetCommand
import guided.{AddGuidedResolventCommand, GetGuidedClausesCommand,IsGuidedNotFoundCommand,SetGuidedFoundCommand}
import sequents.RefutationReachedCommand._
import base.BranchCommand._
import robinson.ParamodulationCommand._
import robinson._
import base._
import logical.DeterministicAndCommand
import scala.collection._
import refinements.base.SequentsMacroCommand._
import refinements.base.SequentsMacroCommand

  //TODO: i'm not sure, why the other publishing buffers are robinsonproofs -- since we cannot upcast here and the gmap
  // only holds resolution proofs, i'm not sure what is better
case class SetClauseWithProofCommand(clauses : Iterable[ResolutionProof[Clause]]) extends DataCommand[Clause] {
  def apply(state:State, data: Any) = {
    val pb = new PublishingBuffer[ResolutionProof[Clause]]
    clauses.foreach(x => pb += x )
    List((state += new Tuple2("clauses", pb), data))
  }
}

case class SetTargetClause2[V <: Sequent](val clause: Clause) extends DataCommand[V] {
  def apply(state: State, data: Any) = List((state += new Tuple2("targetClause", clause.toFSequent), data))
}


case class ReplayCommand(parentIds: Iterable[String], id: String, cls: FSequent) extends DataCommand[Clause] {
  def apply(state: State, data: Any) = {
    import Stream.cons
    //println("\nReplayCommand")
    //get guided clauses mapping from id to resolution proof of id
    //println("\nTarget clause :"+id+"\nfrom "+parentIds.toList)
    val gmap = state("gmap").asInstanceOf[mutable.Map[String,ResolutionProof[Clause]]]
    //println("\nData="+data)
    //println("\nTarget clause="+cls)


    val gproofs = (parentIds.toList).filterNot (_ == "-1") map gmap

    //val target : Clause = if (id == "-1") Clause(Nil,Nil) else Clause(cls.antecedent, cls.succedent)
    //println("\nTrying to prove  "+cls+"  from :")
    gproofs map (x => println(x.root))


    //initialize new prover to spawn -- same as proveFOL in cli
    val prover = new Prover[Clause] {}


    def stream1:  Stream[Command[Clause]] = cons(SequentsMacroCommand[Clause](
      SimpleRefinementGetCommand[Clause],
      List(VariantsCommand, DeterministicAndCommand[Clause](
        List(ApplyOnAllPolarizedLiteralPairsCommand[Clause], ResolveCommand(FOLUnificationAlgorithm), FactorCommand(FOLUnificationAlgorithm)),
        List(ParamodulationCommand(FOLUnificationAlgorithm))),
        SimpleForwardSubsumptionCommand[Clause](new StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm}),
        SimpleBackwardSubsumptionCommand[Clause](new StillmanSubsumptionAlgorithm[FOLExpression] {val matchAlg = FOLMatchingAlgorithm}),
        InsertResolventCommand[Clause]),
      RefutationReachedCommand[Clause]), stream1)
      //RefutationReachedCommand is replaced by SubsumedTargedReachedCommand
//        SubsumedTargedReachedCommand[Clause]), stream1)


//    prover.refute(cons(SetClauseWithProofCommand(gproofs), cons(  SetTargetClause(cls), cons( SubsumedTargedSetFromClauseSetCommand(), stream1)))).next match {
    prover.refute(cons(SetClauseWithProofCommand(gproofs), cons(  SetTargetClause(cls),  stream1))).next match {
      case Some(r) =>
        //println("Found a refutation: "+r.toString)
        gmap(id) = r      //add new id to the guidance map
        List( (state, r) )

      case _ => //println("Replay failed!");
        List(  ) //need to signal failure!
    } 
  }

  override def toString = "ReplayCommand New(" + parentIds + ")"
}


  // we dont have subsumption as it might prevent reaching the exact clause we look for
  case class OldReplayCommand(parentIds: Iterable[String], id: String, cls: FSequent) extends DataCommand[Clause] {
    def apply(state: State, data: Any) = {
      //println("replay: " + parentIds + " - " + id + " - target: " + cls)
      def stream1: Stream[Command[Clause]] =
        Stream.cons(SimpleRefinementGetCommand[Clause],
          Stream.cons(VariantsCommand,
          Stream.cons(ClauseFactorCommand(FOLUnificationAlgorithm),
          Stream.cons(DeterministicAndCommand[Clause]((
            List(ApplyOnAllPolarizedLiteralPairsCommand[Clause], ResolveCommand(FOLUnificationAlgorithm)),
            List(ParamodulationCommand(FOLUnificationAlgorithm)))),
          Stream.cons(IsGuidedNotFoundCommand,
          Stream.cons(InsertResolventCommand[Clause],
          Stream.cons(PrependOnCondCommand[Clause](
            (s: State,d: Any) => {
              val gtf = s.isDefinedAt("guided_target_found")
              val fveq = fvarInvariantMSEquality(d.asInstanceOf[RobinsonResolutionProof].root, s("targetClause").asInstanceOf[FSequent])
                if (fveq) s("guided_target_found") = true
              !gtf && fveq
            } ,
              RestoreCommand[Clause](AddGuidedResolventCommand(id)::InsertResolventCommand[Clause]::RefutationReachedCommand[Clause]::Nil)::Nil),
          stream1))))))
        )
      List((state,Stream.cons(GetGuidedClausesCommand(parentIds), Stream.cons(SetClausesFromDataCommand, Stream.cons(SetTargetClause(cls), stream1)))))
    }

    override def toString = "ReplayCommand("+parentIds+", " + id + ", " +cls+ ")"
  }
}
