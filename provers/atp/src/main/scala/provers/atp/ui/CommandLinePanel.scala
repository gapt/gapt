/*
 * CommandLinePanel.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.ui

import at.logic.provers.atp.commands._
import at.logic.calculi.resolution.base._

import scala.util.parsing.combinator.JavaTokenParsers

object CommandLinePanel {

  def getNextCommand(com:Command, elements: Option[Iterator[Clause]]): Command = com match {
    case ErrorCom(msg) => Console.println("Error: " + msg); manageError(msg)
    case HelpCom => Console.println(HELP_MENU); AppendCommandsCom(InteractCom::Nil)
    case ShowClausesCom => Console.println("List of clauses:"); Console.print(elements.get.zipWithIndex.map(x => x._2 + ": " + x._1 + "\n").mkString); AppendCommandsCom(InteractCom::Nil)
    case EmptyCom => Console.println("Welcome to ATP, please input help for a list of commands"); new TextualCommandsParser {} .parse
    case ResolventFoundReply(res) => Console.println("Resolvent found!: " + res); AppendCommandsCom(InteractCom::Nil)
    case NoResolventFoundReply => Console.println("No resolvent found!"); AppendCommandsCom(InteractCom::Nil)
    case _ => Console.println("Unknown command: " + com); ExitCom
  }

  val EXIT_MSG = "Are you sure you want to exit? [Y/N]"
  val EXIT_REP_Y = List("Y", "y", "Yes")
  val EXIT_REP_N = List("N", "n", "No")
  val HELP_MENU =
    "exit                                     - quit the program\n" +
    "help                                     - this message\n" +
    "clauses = [{c1. c2.}/file_name]          - set the clauses from the list or file\n" +
    "ref = [simple/unit]                      - sets the refinement type\n" +
    /*"parser = [simple/unit]                 - sets the refinement type\n" +*/
    "limit = <time limit>                     - sets the time limit in seconds\n" +
    "init <filename>                          - default inialization sequence with given file name (of clauses)\n" +
    "loop n <?commands sequence>              - loop the command sequences (set by the user or default if nothing is selected) n times\n" +
    "choose n1 n2 <?commands sequence>        - execute once the command sequences (set by the user or default if nothing is selected) on the selected indices of clauses\n" +
    "show                                     - a list of the current clauses\n"

  val NORMAL_MSG_ID = 0
  val EXIT_MSG_ID = 1
  var lastMessage = NORMAL_MSG_ID
  
  private def manageError(msg: String): Command = lastMessage match {
    case EXIT_MSG_ID if msg == EXIT_MSG => manageError(Console.readLine)
    case EXIT_MSG_ID if EXIT_REP_Y.contains(msg) => ExitCom
    case EXIT_MSG_ID if EXIT_REP_N.contains(msg) => {lastMessage = NORMAL_MSG_ID; AppendCommandsCom(InteractCom::Nil)}
    case EXIT_MSG_ID => {Console.println("Unknown reply, please type again"); manageError(Console.readLine)}
    case _ => AppendCommandsCom(InteractCom::Nil)
  }
}

/* ------------------------------------------------------------------------- */
import scala.util.parsing.combinator.RegexParsers
import at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
import at.logic.parsing.readers.{StringReader,FileReader}

object commandsMap extends scala.collection.mutable.HashMap[String, List[Command]] {
  put("def", List(CreateVariantCom, AndCom(
        ApplyOnAllPolarizedLiteralPairsCom(ResolveCom::ApplyOnAllFactorsCom(IfNotTautologyCom::IfNotForwardSubsumedCom::BackwardSubsumptionCom::InsertCom::Nil)::Nil)::Nil,
        ApplyOnAllPositiveEitherLiteralPairsCom(IfFirstLiteralIsEqualityCom::ApplyOnAllSecondLiteralNonVarSubterms(ParamodulateCom::IfNotTautologyCom::IfNotForwardSubsumedCom::BackwardSubsumptionCom::InsertCom::Nil)::Nil)::Nil)))
}

trait TextualCommandsParser extends RegexParsers with JavaTokenParsers {
  def parse: Command = {
    parseAll(command, Console.readLine).get
  }
  protected def command: Parser[Command] = init | help | show | exit | setClauses | setRefinement | /*setParser |*/ setTimeLimit | loopNTimes | choose | unknown

  protected def init: Parser[Command] = "init" ~> """.*""".r ^^ {case a => AppendCommandsCom(
        SetClausesCom((new FileReader(a) with SimpleResolutionParserFOL).getClauseList)::
        SetRefinementCom(createSimple)::
        SetCommandsParserCom(new at.logic.provers.atp.commandsParsers.FOLResolutionCommandsParser{})::
        SetSubsumptionManagerCom(createSubsum)::
        InteractCom::Nil)}

  // here we use ^^ instead of ^^^ because we want the value to be recomptued every time as we change there a global value
  protected def exit: Parser[Command] = "exit" ^^ {_ => {CommandLinePanel.lastMessage =  CommandLinePanel.EXIT_MSG_ID; AppendCommandsCom(ErrorCom(CommandLinePanel.EXIT_MSG)::Nil)}}
  protected def help: Parser[Command] = "help" ^^^ (AppendCommandsWithLastCom(HelpCom, InteractCom::Nil))
  protected def show: Parser[Command] = "show" ^^^ (AppendCommandsWithLastCom(ShowClausesCom, InteractCom::Nil))

  protected def setClauses: Parser[Command] = "clauses" ~ "=" ~ (clausesList | clausesInFile) ^^ {case "clauses" ~ "=" ~ lst => AppendCommandsCom(SetClausesCom(lst)::InteractCom::Nil)}
  private def clausesList: Parser[List[Clause]] = "{" ~> """.*""".r <~ "}" ^^ (a => (new StringReader(a) with SimpleResolutionParserFOL).getClauseList)
  private def clausesInFile: Parser[List[Clause]] = """.*""".r ^^ (a => (new FileReader(a) with SimpleResolutionParserFOL).getClauseList)

  protected def setRefinement: Parser[Command] = "ref" ~ "=" ~ ref ^^ {case "ref" ~ "=" ~ ref => AppendCommandsCom(SetRefinementCom(ref)::InteractCom::Nil)}
  /*protected def setParser: Parser[Command] = "parser" ~ "=" ~ parser ^^ {case "ref" ~ "=" ~ parser => AppendCommandsCom(SetRefinementCom(ref)::InteractCom::Nil)}*/
  protected def setTimeLimit: Parser[Command] = "limit" ~ "=" ~ wholeNumber ^^ {case "limit" ~ "=" ~ num  => AppendCommandsCom(SetTimeLimit(num.toInt * 1000)::InteractCom::Nil)}
  
  protected def loopNTimes: Parser[Command] = "loop" ~> wholeNumber ~ """.*""".r ^^ {case num ~ name => {val coms = commandsMap((if (name != "") name else "def")); AppendCommandsCom((1 to num.toInt).flatMap(_ => GetClausesCom::coms).toList:::InteractCom::Nil) }}
  protected def choose: Parser[Command] = "choose" ~> wholeNumber ~ wholeNumber ~ """.*""".r ^^ {case num1 ~ num2 ~ name => {val coms = commandsMap((if (name != "") name else "def")); AppendCommandsCom(ChooseClausesCom(num1.toInt, num2.toInt)::coms:::InteractCom::Nil) }}

  protected def unknown: Parser[Command] = """.*""".r ^^ (msg => AppendCommandsCom(ErrorCom("Unknown command: " + msg + "!")::Nil))

  import at.logic.utils.ds.PublishingBuffer
  import at.logic.provers.atp.refinements._

  private def ref: Parser[PublishingBuffer[Clause] => Refinement] = simpleRef | unitRef

  private def simpleRef: Parser[PublishingBuffer[Clause] => Refinement] = "simple"  ^^ (x => createSimple)
  private def unitRef: Parser[PublishingBuffer[Clause] => Refinement] = "unit"  ^^ (x => createUnit)

  private def createSimple(pb: PublishingBuffer[Clause]): Refinement = new SimpleRefinement(pb)
  private def createUnit(pb: PublishingBuffer[Clause]): Refinement = new UnitRefinement(pb)
  private def createSubsum(pb: PublishingBuffer[Clause]): at.logic.algorithms.subsumption.managers.SubsumptionManager =
    new at.logic.algorithms.subsumption.managers.SimpleManager(pb.asInstanceOf[PublishingBuffer[at.logic.calculi.lk.base.Sequent]],
                        new at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithm{val matchAlg = at.logic.algorithms.matching.fol.FOLMatchingAlgorithm})
}
