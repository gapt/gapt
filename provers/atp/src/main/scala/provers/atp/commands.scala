/*
 * commands.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp

import at.logic.calculi.resolution.base._

package commands {

  object theEmptyClause{
    def apply(): ResolutionProof = Axiom(Clause(Nil,Nil))
  }
  
  sealed abstract class Command
  case object EmptyCom extends Command
  case class InsertClausesCom(clauses: List[Clause]) extends Command
  case object GetClausesCom extends Command
  case object FailureCom extends Command
  case class ApplyOnClausesCom(clauses: Tuple2[ResolutionProof, ResolutionProof]) extends Command
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
  case class SetUnificationAlgorithmCom(alg: at.logic.unification.UnificationAlgorithm) extends Command
  
  // default commands streams
  object AutomatedFOLStream {
    def apply(clauses: List[Clause]) = 
      // the setting of the algorithm is not required as we set a default one in the commands parser
      //Stream.cons(SetUnificationAlgorithmCom(at.logic.unification.fol.FOLUnificationAlgorithm),
      Stream.cons(InsertClausesCom(clauses),rest)//)
    def rest: Stream[Command] = Stream(
      GetClausesCom,
      ApplyOnAllLiteralPairsCom(ResolveCom::InsertCom::Nil)
    ).append(rest)
  }
}
