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
import at.logic.language.hol.HOLExpression

package commands {

  object theEmptyClause{
    def apply(): ResolutionProof = Axiom(Clause(Nil,Nil))
  }
  
  sealed abstract class Command

  abstract class Reply extends Command // replies from Prover
  abstract class Com extends Command // commands to prover

  case object EmptyCom extends Command
  case class ErrorCom(msg: String) extends Command
  case class SetTimeLimit(time: Long) extends Command
  case class SetUICom(u: UserInterface) extends Command
  case class SetCommandsParserCom(cp: CommandsParser) extends Command
  case class InsertClausesCom(clauses: List[Clause]) extends Command
  case object GetClausesCom extends Command
  case object FailureCom extends Command
  case object ExitCom extends Command
  case object HelpCom extends Command
  case object ShowClausesCom extends Command
  //case class ApplyOnClausesCom(clauses: Tuple2[ResolutionProof, ResolutionProof]) extends Command
  case object FactorCom extends Command
  case object ResolveCom extends Command
  case object ParamodulateCom extends Command
  case object ParamodulateOnLiteralCom extends Command
  abstract class ResultedClauseCom(val proof: ResolutionProof) extends Command
  object ResultedClauseCom {
    def unapply(com: Command) = com match {
      case c: ResultedClauseCom => Some(c.proof)
      case _ => None
    }
  }
  case class ResolventCom(resolvent: ResolutionProof) extends ResultedClauseCom(resolvent)
  case class ParamodulantCom(paramodulant: ResolutionProof) extends ResultedClauseCom(paramodulant)
  abstract class NoResultedClauseCom extends Command
  object NoResultedClauseCom {
    def apply() = new NoResultedClauseCom {} // when the subclass information is not important we can generate the superclass
    def unapply(com: Command): Boolean = com match {
      case c: NoResultedClauseCom => true
      case _ => false
    }
  }
  case object NoResolventCom extends NoResultedClauseCom
  case object NoParamodulantCom extends NoResultedClauseCom
  case object InsertCom extends Command
  case class SetTargetResolventCom(target: ResolutionProof) extends Command
  case class ApplyOnAllPolarizedLiteralPairsCom(ls: List[Command]) extends Command
  case class ApplyOnAllLiteralPairsCom(ls: List[Command]) extends Command
  case class ApplyOnAllPositiveEitherLiteralPairsCom(ls: List[Command]) extends Command // one must be positive at least
  case class ApplyOnAllSecondLiteralNonVarSubterms(ls: List[Command]) extends Command
  case class AppendCommandsCom(ls: Seq[Command]) extends Command
  case class AppendCommandsWithLastCom(last:Command, ls: Seq[Command]) extends Command
  case class ApplyOnLiteralPositionCom(pos: Tuple2[Int,Int], clauses: Tuple2[ResolutionProof, ResolutionProof]) extends Command
  case class ApplyOnSecondSubtermCom(pos: Tuple2[Int,Int], clauses: Tuple2[ResolutionProof, ResolutionProof], posi: List[Int], subterm: HOLExpression) extends Command
  case class SetUnificationAlgorithmCom(alg: at.logic.algorithms.unification.UnificationAlgorithm) extends Command
  case class ApplyOnAllFactorsCom(ls: List[Command]) extends Command
  //case class ApplyOnAllClausePairsOnLiteralPairs(ls: List[Command]) extends Command
  case object CreateVariantCom extends Command
  case class GotClausesPairCom(clauses: Tuple2[ResolutionProof, ResolutionProof]) extends Command
  case class GotListOfClausePairsCom(clausePairs: List[Tuple2[ResolutionProof, ResolutionProof]]) extends Command
  case object IfNotTautologyCom extends Command
  case object IfFirstLiteralIsEqualityCom extends Command
  // logical commands
  case class AndCom(c1: List[Command], c2: List[Command]) extends Command
  case object InteractCom extends Command

  // clauses commands
  case class SetClausesCom(clauseList: List[Clause]) extends Command

  // refinement commands
  case class SetRefinementCom(refCreator: at.logic.utils.ds.PublishingBuffer[Clause] => at.logic.provers.atp.refinements.Refinement) extends Command

  // subsumption commands
  case class SetSubsumptionManagerCom(subsumCreator: at.logic.utils.ds.PublishingBuffer[Clause] => at.logic.algorithms.subsumption.managers.SubsumptionManager) extends Command
  case object IfNotForwardSubsumedCom extends Command
  case object BackwardSubsumptionCom extends Command

  // commands to prover
  case class CorrectResolventFoundCom(res: ResolutionProof) extends Com // not exactly a command to prover, fix that
  case class ChooseClausesCom(c1: Int, c2: Int) extends Com // indices from the publishing buffer

  // replies from prover
  case class ResolventFoundReply(res: ResolutionProof) extends Reply
  case object NoResolventFoundReply extends Reply

  /*
   * If commands have one result only then they should be specified sequentially. I.e. GetClauseCom and then apply
   * on the result CreateVariantCom. If the command generates several results then the commands to be applied on
   * each result should be passed as arguments
   */
  // default commands streams
  object AutomatedFOLStream {
    def apply(timeLimit: Long,
              clausesList: List[Clause],
              refCreator: at.logic.utils.ds.PublishingBuffer[Clause] => at.logic.provers.atp.refinements.Refinement,
              subsumCreator: at.logic.utils.ds.PublishingBuffer[Clause] => at.logic.algorithms.subsumption.managers.SubsumptionManager): Stream[Command] =
      Stream.cons(SetTimeLimit(timeLimit),
      Stream.cons(SetClausesCom(clausesList),
      Stream.cons(SetRefinementCom(refCreator),
      Stream.cons(SetSubsumptionManagerCom(subsumCreator),
      Stream.cons(SetCommandsParserCom(new at.logic.provers.atp.commandsParsers.FOLResolutionCommandsParser{}), rest)))))
    def rest: Stream[Command] = Stream(
      GetClausesCom, CreateVariantCom, AndCom(
        ApplyOnAllPolarizedLiteralPairsCom(ResolveCom::ApplyOnAllFactorsCom(IfNotTautologyCom::IfNotForwardSubsumedCom::BackwardSubsumptionCom::InsertCom::Nil)::Nil)::Nil,
        ApplyOnAllPositiveEitherLiteralPairsCom(IfFirstLiteralIsEqualityCom::ApplyOnAllSecondLiteralNonVarSubterms(ParamodulateCom::IfNotTautologyCom::IfNotForwardSubsumedCom::BackwardSubsumptionCom::InsertCom::Nil)::Nil)::Nil)
    ).append(rest)
  }
}
