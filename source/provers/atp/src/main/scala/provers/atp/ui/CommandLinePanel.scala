/*
 * CommandLinePanel.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.ui

import at.logic.utils.ds._
import at.logic.provers.atp.commands._
import at.logic.calculi.resolution.base._
import at.logic.calculi.lk.base.Sequent
import scala.util.parsing.combinator.JavaTokenParsers
import scala.util.parsing.combinator.RegexParsers
import at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
import at.logic.parsing.readers.{StringReader,FileReader}
import at.logic.provers.atp.refinements._

object Settings {
  val EXIT_MSG = "Are you sure you want to exit? [Y/N]"
  val EXIT_REP_Y = List("Y", "y", "Yes")
  val EXIT_REP_N = List("N", "n", "No")
  val NORMAL_MSG_ID = 0
  val EXIT_MSG_ID = 1
  var lastMessage = NORMAL_MSG_ID


}
trait CommandLinePanel[V <: Sequent] extends UIPanel[V]{

  def getNextCommand(com:Command, elements: Option[Iterator[V]]): Command = com match {
    case ErrorReply(msg) => Console.println("Error: " + msg); manageError(msg)
    case HelpCom => Console.println(HELP_MENU + "\n" + getHelpMenu); AppendCommandsCom(InteractCom::Nil)
    case ShowClausesCom => Console.println("List of clauses:"); Console.print(elements.get.zipWithIndex.map(x => x._2 + ": " + x._1 + "\n").mkString); AppendCommandsCom(InteractCom::Nil)
    case ResolventFoundReply(res) => Console.println("Resolvent found!: " + res); AppendCommandsCom(InteractCom::Nil)
    case NoResolventFoundReply => Console.println("No resolvent found!"); AppendCommandsCom(InteractCom::Nil)
    case EmptyCom => handleCommand
  }

  protected def getHelpMenu: String
  protected def handleCommand: Command

  
  val HELP_MENU =
    "exit                                     - quit the program\n" +
    "help                                     - this message\n" +
    "clauses = [{c1. c2.}/file_name]          - set the clauses from the list or file\n" +
    "ref = [simple/unit]                      - sets the refinement type\n" +
    "limit = <time limit>                     - sets the time limit in seconds\n" +
    "init <filename>                          - default inialization sequence with given file name (of clauses)\n" +
    "show                                     - a list of the current clauses\n"

  private def manageError(msg: String): Command = Settings.lastMessage match {
    case Settings.EXIT_MSG_ID if msg == Settings.EXIT_MSG => manageError(Console.readLine)
    case Settings.EXIT_MSG_ID if Settings.EXIT_REP_Y.contains(msg) => ExitCom
    case Settings.EXIT_MSG_ID if Settings.EXIT_REP_N.contains(msg) => {Settings.lastMessage =Settings. NORMAL_MSG_ID; AppendCommandsCom(InteractCom::Nil)}
    case Settings.EXIT_MSG_ID => {Console.println("Unknown reply, please type again"); manageError(Console.readLine)}
    case _ => AppendCommandsCom(InteractCom::Nil)
  }
}

/* ------------------------------------------------------------------------- */

trait TextualCommandsParser[V <: Sequent] extends RegexParsers with JavaTokenParsers {
  def parse: Command = {
    parseAll(command, Console.readLine).get
  }
  protected def command: Parser[Command] = init | help | show | exit | setClauses | setRefinement | /*setParser |*/ setTimeLimit | custom | unknown

 // here we use ^^ instead of ^^^ because we want the value to be recomptued every time as we change there a global value
  protected def exit: Parser[Command] = "exit" ^^ {_ => {Settings.lastMessage =  Settings.EXIT_MSG_ID; AppendCommandsCom(ErrorReply(Settings.EXIT_MSG)::Nil)}}
  protected def help: Parser[Command] = "help" ^^^ (AppendCommandsWithLastCom(HelpCom, InteractCom::Nil))
  protected def show: Parser[Command] = "show" ^^^ (AppendCommandsWithLastCom(ShowClausesCom, InteractCom::Nil))

  protected def setClauses: Parser[Command] = "clauses" ~ "=" ~ (clausesList | clausesInFile) ^^ {case "clauses" ~ "=" ~ lst => AppendCommandsCom(SetClausesCom(lst)::InteractCom::Nil)}

  protected def setRefinement: Parser[Command] = "ref" ~ "=" ~ ref ^^ {case "ref" ~ "=" ~ ref => AppendCommandsCom(SetRefinementCom(ref)::InteractCom::Nil)}
  /*protected def setParser: Parser[Command] = "parser" ~ "=" ~ parser ^^ {case "ref" ~ "=" ~ parser => AppendCommandsCom(SetRefinementCom(ref)::InteractCom::Nil)}*/
  protected def setTimeLimit: Parser[Command] = "limit" ~ "=" ~ wholeNumber ^^ {case "limit" ~ "=" ~ num  => AppendCommandsCom(SetTimeLimit(num.toInt * 1000)::InteractCom::Nil)}

  protected def clausesList: Parser[List[V]]
  protected def clausesInFile: Parser[List[V]]
  protected def custom: Parser[Command]
  protected def ref: Parser[PublishingBuffer[V] => Refinement[V]]
  protected def init: Parser[Command]

  protected def unknown: Parser[Command] = """.*""".r ^^ (msg => AppendCommandsCom(ErrorReply("Unknown command: " + msg + "!")::Nil))
}
