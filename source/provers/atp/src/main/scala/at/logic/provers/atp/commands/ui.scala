package at.logic.provers.atp.commands


/**
 * Created by IntelliJ IDEA.
 * User: shaolin
 * Date: Dec 20, 2010
 * Time: 4:14:33 PM
 * To change this template use File | Settings | File Templates.
 */

package ui {
import _root_.at.logic.calculi.lk.base.Sequent
import _root_.at.logic.provers.atp.commands.base.InitialCommand
import at.logic.provers.atp.Definitions._
  import scala.io.StdIn

  case class getTwoClausesFromUICommand[V <: Sequent](ui: Seq[Sequent] => Tuple2[Int,Int]) extends InitialCommand[V] {
    def apply(state: State) = {
      val clauses = state("clauses").asInstanceOf[Seq[Sequent]]
      val reply = ui(clauses)
      List((state, (clauses(reply._1), clauses(reply._2))))
    }
  }

  object PromptTerminal {
    object GetTwoClauses extends Function1[Seq[Sequent], Tuple2[Int,Int]] {
      def apply(seq: Seq[Sequent]): Tuple2[Int,Int] = {
        Console.println("List of clauses in set:")
        seq.zipWithIndex.foreach(x => Console.println(x._2 + ") " + x._1))
        Console.print("Enter index of first clause: " ); val ind1 = StdIn.readInt()
        Console.print("Enter index of second clause: " ); val ind2 = StdIn.readInt()
        (ind1, ind2)
      }
    }
  }
}
