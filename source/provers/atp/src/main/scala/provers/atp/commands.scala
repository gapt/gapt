/*
 * commands.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp

import at.logic.calculi.resolution.base._
import at.logic.provers.atp.commandsParsers.CommandsParser
import at.logic.language.hol.HOLExpression
import at.logic.calculi.lk.base._
package commands {

  object theEmptyClause{
    def apply(): ResolutionProof[Sequent] = InitialSequent(Sequent(Nil,Nil))
  }
  
  abstract class Command

  abstract class Reply extends Command // replies from Prover
  abstract class Com extends Command // commands to prover

  // coms
  case object EmptyCom extends Com
  case class SetTimeLimit(time: Long) extends Com
  case class SetCommandsParserCom(cp: CommandsParser) extends Com
  case class InsertClausesCom[V <: Sequent](clauses: List[V]) extends Com
  case object GetClausesCom extends Com
  case object ExitCom extends Com
  case object HelpCom extends Com
  case object ShowClausesCom extends Com
  case object InsertCom extends Com
  case class SetTargetResolventCom[V <: Sequent](target: ResolutionProof[V]) extends Com
  case class ApplyOnAllPolarizedLiteralPairsCom(ls: List[Com]) extends Com
  case class ApplyOnAllLiteralPairsCom(ls: List[Com]) extends Com
  case class ApplyOnAllPositiveEitherLiteralPairsCom(ls: List[Com]) extends Com // one must be positive at least
  case class ApplyOnAllSecondLiteralNonVarSubterms(ls: List[Com]) extends Com
  case class AppendCommandsCom(ls: Seq[Command]) extends Com
  case class AppendCommandsWithLastCom(last:Command, ls: Seq[Command]) extends Com
  case class ApplyOnLiteralPositionCom[V <: Sequent](pos: Tuple2[Int,Int], clauses: Tuple2[ResolutionProof[V], ResolutionProof[V]]) extends Com
  case class ApplyOnSecondSubtermCom[V <: Sequent](pos: Tuple2[Int,Int], clauses: Tuple2[ResolutionProof[V], ResolutionProof[V]], posi: List[Int], subterm: HOLExpression) extends Com
  case class SetUnificationAlgorithmCom(alg: at.logic.algorithms.unification.UnificationAlgorithm) extends Com
  case object IfNotTautologyCom extends Com
  case object IfFirstLiteralIsEqualityCom extends Com
  case class AndCom(c1: List[Com], c2: List[Com]) extends Com
  case object InteractCom extends Com
  // clauses commands
  case class SetClausesCom[V <: Sequent](clauseList: List[V]) extends Com
  // refinement commands
  case class SetRefinementCom[V <: Sequent](refCreator: at.logic.utils.ds.PublishingBuffer[V] => at.logic.provers.atp.refinements.Refinement[V]) extends Com
  // subsumption commands
  case class SetSubsumptionManagerCom[V <: Sequent](subsumCreator: at.logic.utils.ds.PublishingBuffer[V] => at.logic.algorithms.subsumption.managers.SubsumptionManager) extends Com
  case object IfNotForwardSubsumedCom extends Com
  case object BackwardSubsumptionCom extends Com
  case class ChooseClausesCom(c1: Int, c2: Int) extends Com // indices from the publishing buffer
  //
  // replies
  case class ErrorReply(msg: String) extends Reply
  case object FailureReply extends Reply
  case class GotClausesPairReply[V <: Sequent](clauses: Tuple2[ResolutionProof[V], ResolutionProof[V]]) extends Reply
  abstract class ResultedClauseReply[V <: Sequent](val proof: ResolutionProof[V]) extends Reply
  object ResultedClauseReply {
    def unapply(com: Command) = com match {
      case c: ResultedClauseReply[_] => Some(c.proof)
      case _ => None
    }
  }
  abstract class NoResultedClauseReply extends Reply
  object NoResultedClauseReply {
    def apply() = new NoResultedClauseReply {} // when the subclass information is not important we can generate the superclass
    def unapply(com: Command): Boolean = com match {
      case c: NoResultedClauseReply => true
      case _ => false
    }
  }
  case class GotListOfClausePairsReply[V <: Sequent](clausePairs: List[Tuple2[ResolutionProof[V], ResolutionProof[V]]]) extends Reply
  case class CorrectResolventFoundReply[V <: Sequent](res: ResolutionProof[V]) extends Reply
  case class ResolventFoundReply[V <: Sequent](res: ResolutionProof[V]) extends Reply
  case object NoResolventFoundReply extends Reply
  /*
   * If commands have one result only then they should be specified sequentially. I.e. GetClauseCom and then apply
   * on the result CreateVariantCom. If the command generates several results then the commands to be applied on
   * each result should be passed as arguments
   */
}
