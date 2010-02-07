/*
 * commands.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp

import at.logic.calculi.resolution.base._
import at.logic.provers.atp.ui.UserInterface
import at.logic.provers.atp.commandsParsers.CommandsParser
import at.logic.provers.atp.refinements.Refinement

package commands {

  object theEmptyClause{
    def apply(): ResolutionProof = Axiom(Clause(Nil,Nil))
  }
  
  sealed abstract class Command
  case object EmptyCom extends Command
  case class ErrorCom(msg: String) extends Command
  case class SetTimeLimit(time: Long) extends Command
  case class SetUICom(u: UserInterface) extends Command
  case class SetRefinementCom(r: Refinement) extends Command
  case class SetCommandsParserCom(cp: CommandsParser) extends Command
  case class InsertClausesCom(clauses: List[Clause]) extends Command
  case object GetClausesCom extends Command
  case object FailureCom extends Command
  //case class ApplyOnClausesCom(clauses: Tuple2[ResolutionProof, ResolutionProof]) extends Command
  case object FactorCom extends Command
  case object ResolveCom extends Command
  case class ResolventCom(resolvent: ResolutionProof) extends Command
  case object NoResolventCom extends Command
  case object InsertCom extends Command
  case class CorrectResolventFound(res: ResolutionProof) extends Command
  case class SetTargetResolventCom(target: ResolutionProof) extends Command
  case class ApplyOnAllLiteralPairsCom(ls: List[Command]) extends Command
  case class AppendCommandsCom(ls: Seq[Command]) extends Command
  case class ApplyOnLiteralPositionCom(pos: Tuple2[Int,Int], clauses: Tuple2[ResolutionProof, ResolutionProof]) extends Command
  case class SetUnificationAlgorithmCom(alg: at.logic.algorithms.unification.UnificationAlgorithm) extends Command
  case class ApplyOnAllFactorsCom(ls: List[Command]) extends Command
  //case class ApplyOnAllClausePairsOnLiteralPairs(ls: List[Command]) extends Command
  case object CreateVariantCom extends Command
  case class GotClausesPairCom(clauses: Tuple2[ResolutionProof, ResolutionProof]) extends Command
  case class GotListOfClausePairsCom(clausePairs: List[Tuple2[ResolutionProof, ResolutionProof]]) extends Command

  // default commands streams
  object AutomatedFOLStream {
    def apply(clauses: List[Clause]): Stream[Command] = apply(clauses, -1)
    def apply(clauses: List[Clause], timeLimit: Long): Stream[Command] =
      Stream.cons(SetTimeLimit(timeLimit),
        Stream.cons(SetUICom(new at.logic.provers.atp.ui.CommandLineUserInterface{}),
          Stream.cons(SetRefinementCom(new at.logic.provers.atp.refinements.SimpleRefinement{}),
            Stream.cons(SetCommandsParserCom(new at.logic.provers.atp.commandsParsers.FOLResolutionCommandsParser{}),
              Stream.cons(InsertClausesCom(clauses),rest) )))
      )
    def rest: Stream[Command] = Stream(
      GetClausesCom, CreateVariantCom,
      ApplyOnAllLiteralPairsCom(ResolveCom::ApplyOnAllFactorsCom(InsertCom::Nil)::Nil)
    ).append(rest)
  }
}
