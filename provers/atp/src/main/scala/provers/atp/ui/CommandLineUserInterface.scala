/*
 * CommandLineUserInterface.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.ui
import at.logic.provers.atp.commands._

trait CommandLineUserInterface extends UserInterface {
  def parse(cmd: Command) = cmd match {
    case ErrorCom(msg) => Console.println(msg); FailureCom
    case _ => cmd
  }
}
