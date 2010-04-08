/*
 * RobinsonCommandLinePanel.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.provers.atp.ui

import at.logic.calculi.resolution.robinson._
import at.logic.provers.atp.commands._
import at.logic.provers.atp.commandsParsers.RobinsonCommandsParser
import at.logic.provers.atp.commandsParsers.robinson._
import at.logic.utils.ds.PublishingBuffer
import at.logic.provers.atp.refinements._

object RobinsonCommandLinePanel extends CommandLinePanel[Clause] {

  val HELP_MENU2 =
    "loop n <?commands sequence>              - loop the command sequences (set by the user or default if nothing is selected) n times\n" +
    "choose n1 n2 <?commands sequence>        - execute once the command sequences (set by the user or default if nothing is selected) on the selected indices of clauses\n"
    
  protected def getHelpMenu: String = HELP_MENU2
  protected def handleCommand = {Console.println("Welcome to ATP, please input help for a list of commands"); RobinsonParser.parse}

  import scala.util.parsing.combinator.RegexParsers
  import at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
  import at.logic.parsing.readers.{StringReader,FileReader}
}

import scala.util.parsing.combinator.RegexParsers
import at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
import at.logic.parsing.readers.{StringReader,FileReader}

private[ui] object RobinsonParser extends TextualCommandsParser[Clause] {

  object commandsMap extends scala.collection.mutable.HashMap[String, List[Command]] {
    put("def", List(CreateVariantCom, AndCom(
        ApplyOnAllPolarizedLiteralPairsCom(ResolveCom::ApplyOnAllFactorsCom(IfNotTautologyCom::IfNotForwardSubsumedCom::BackwardSubsumptionCom::InsertCom::Nil)::Nil)::Nil,
        ApplyOnAllPositiveEitherLiteralPairsCom(IfFirstLiteralIsEqualityCom::ApplyOnAllSecondLiteralNonVarSubterms(ParamodulateCom::IfNotTautologyCom::IfNotForwardSubsumedCom::BackwardSubsumptionCom::InsertCom::Nil)::Nil)::Nil)))
  }
  
  def init: Parser[Command] = "init" ~> """.*""".r ^^ {case a => AppendCommandsCom(
        SetClausesCom((new FileReader(a) with SimpleResolutionParserFOL).getClauseList)::
        SetRefinementCom(createSimple)::
        SetCommandsParserCom(at.logic.provers.atp.commandsParsers.RobinsonCommandsParser)::
        SetSubsumptionManagerCom(createSubsum)::
        InteractCom::Nil)}

  def custom: Parser[Command] = loopNTimes | choose

  def clausesList: Parser[List[Clause]] = "{" ~> """.*""".r <~ "}" ^^ (a => (new StringReader(a) with SimpleResolutionParserFOL).getClauseList)
  def clausesInFile: Parser[List[Clause]] = """.*""".r ^^ (a => (new FileReader(a) with SimpleResolutionParserFOL).getClauseList)

  def loopNTimes: Parser[Command] = "loop" ~> wholeNumber ~ """.*""".r ^^ {case num ~ name => {val coms = commandsMap((if (name != "") name else "def")); AppendCommandsCom((1 to num.toInt).flatMap(_ => GetClausesCom::coms).toList:::InteractCom::Nil) }}
  def choose: Parser[Command] = "choose" ~> wholeNumber ~ wholeNumber ~ """.*""".r ^^ {case num1 ~ num2 ~ name => {val coms = commandsMap((if (name != "") name else "def")); AppendCommandsCom(ChooseClausesCom(num1.toInt, num2.toInt)::coms:::InteractCom::Nil) }}

  def ref: Parser[PublishingBuffer[Clause] => Refinement[Clause]] = simpleRef | unitRef

  private def simpleRef: Parser[PublishingBuffer[Clause] => Refinement[Clause]] = "simple"  ^^ (x => createSimple)
  private def unitRef: Parser[PublishingBuffer[Clause] => Refinement[Clause]] = "unit"  ^^ (x => createUnit)

  private def createSimple(pb: PublishingBuffer[Clause]): Refinement[Clause] = new SimpleRefinement(pb)
  private def createUnit(pb: PublishingBuffer[Clause]): Refinement[Clause] = new UnitRefinement(pb)
  private def createSubsum(pb: PublishingBuffer[Clause]): at.logic.algorithms.subsumption.managers.SubsumptionManager =
    new at.logic.algorithms.subsumption.managers.SimpleManager(pb.asInstanceOf[PublishingBuffer[at.logic.calculi.lk.base.Sequent]],
                        new at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithm{val matchAlg = at.logic.algorithms.matching.fol.FOLMatchingAlgorithm})
}
