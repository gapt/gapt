package at.logic.provers.atp

import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
import at.logic.provers.atp.commands.robinson.ParamodulationCommand
import org.specs2.mutable._
import at.logic.calculi.resolution.robinson._
import at.logic.language.fol.FOLFormula
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.calculi.lk.base.FSequent
import at.logic.parsing.language.prover9.Prover9TermParser.parseFormula
import at.logic.calculi.resolution.{ResolutionProof, Clause}
import at.logic.provers.atp.commands.sequents._
import at.logic.provers.atp.commands.base._


@RunWith(classOf[JUnitRunner])
class RobinsonTest extends SpecificationWithJUnit {
  "ParamodulationCommand" should  {
    "applying paramodulation command on two res.proofs" in {
      "failing replay command for prime0" in {

        val fseq1 = new MyParser("-=(ladr2(ladr8, x), ladr6) | =(x, ladr7(ladr6, ladr5(ladr1(ladr8, x), ladr8))).").getClauseList

        val fseq2 = new MyParser("=(ladr7(ladr6, ladr5(y, ladr8)), ladr5(y, ladr8)).").getClauseList

        val f2flipseq2 = new MyParser("=(ladr5(y, ladr8), ladr7(ladr6, ladr5(y, ladr8))).").getClauseList
        val rrp1 = InitialClause(fseq1.head.antecedent.map(f => f.asInstanceOf[FOLFormula]), fseq1.head.succedent.map(f => f.asInstanceOf[FOLFormula]))
        val rrp2 = InitialClause(Nil,  fseq2.head.succedent.map(f => f.asInstanceOf[FOLFormula]))
        val rrp2flip = InitialClause(Nil,  f2flipseq2.head.succedent.map(f => f.asInstanceOf[FOLFormula]))
        val l_para = ParamodulationCommand(FOLUnificationAlgorithm).apply(rrp1, rrp2)// must exist(c => {println(c); false})
        ok
      }
    }
  }
}

