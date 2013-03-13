package at.logic.provers.atp

import _root_.at.logic.provers.atp.commands.base.{BranchCommand, Command}
import _root_.at.logic.provers.atp.commands.logical.DeterministicAndCommand
import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
import at.logic.provers.atp.commands.refinements.simple._
import at.logic.provers.atp.commands.refinements.base._
import at.logic.provers.atp.commands.sequents._
import at.logic.provers.atp.commands.robinson._
import org.specs2.mutable._
import at.logic.parsing.calculi.simple.SimpleResolutionParserFOL
import at.logic.parsing.readers.StringReader
import at.logic.calculi.resolution.base._
import at.logic.calculi.resolution.robinson._
import at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithm
import at.logic.algorithms.matching.fol.FOLMatchingAlgorithm
import at.logic.calculi.resolution.robinson.InitialClause._
import at.logic.language.fol.{FOLFormula, FOLExpression}

//private class MyParser(str: String) extends StringReader(str) with SimpleResolutionParserFOL

class RobinsonTest extends SpecificationWithJUnit {
  "ParamodulationCommand" should  {
    "applying paramodulation command on two res.proofs" in {
      "failing replay command for prime0" in {
        //println(Console.BLUE+"\n\n\nRobinsonTest.scala, ParamodulationCommand:\n\n")
        //        val a = new MyParser("=(Ladr5(ladr1(ladr8, x), ladr8), x).").getClauseList

        val fseq1 = new MyParser("-=(ladr2(ladr8, x), ladr6) | =(x, ladr7(ladr6, ladr5(ladr1(ladr8, x), ladr8))).").getClauseList

        val fseq2 = new MyParser("=(ladr7(ladr6, ladr5(y, ladr8)), ladr5(y, ladr8)).").getClauseList

        val f2flipseq2 = new MyParser("=(ladr5(y, ladr8), ladr7(ladr6, ladr5(y, ladr8))).").getClauseList
        val rrp1 = InitialClause(fseq1.head.antecedent.map(f => f.asInstanceOf[FOLFormula]), fseq1.head.succedent.map(f => f.asInstanceOf[FOLFormula]))
        val rrp2 = InitialClause(Nil,  fseq2.head.succedent.map(f => f.asInstanceOf[FOLFormula]))
        val rrp2flip = InitialClause(Nil,  f2flipseq2.head.succedent.map(f => f.asInstanceOf[FOLFormula]))
        val l_para = ParamodulationCommand(FOLUnificationAlgorithm).apply(rrp1, rrp2)// must exist(c => {println(c); false})
        //println("\n\nEnd of ParamodulationCommand"+Console.RESET)
        ok
      }
    }
  }
}
