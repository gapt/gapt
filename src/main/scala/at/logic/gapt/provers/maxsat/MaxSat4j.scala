package at.logic.gapt.provers.maxsat

import java.io.{ ByteArrayInputStream, File, BufferedWriter, FileWriter }
import at.logic.gapt.proofs.HOLClause
import at.logic.gapt.provers.sat4j.readSat4j
import org.parboiled2.ParserInput.ByteArrayBasedParserInput
import org.sat4j.maxsat.reader.WDimacsReader
import org.sat4j.maxsat.WeightedMaxSatDecorator
import org.sat4j.pb.IPBSolver
import org.sat4j.specs.ContradictionException

/**
 * Created by frain on 4/1/15.
 */
class MaxSat4j extends MaxSATSolver {
  def solve( hard: List[HOLClause], soft: List[( HOLClause, Int )] ) = {
    val helper = new WDIMACSHelper( hard, soft )
    val sat4j_in = helper.getWCNFInput().toString()

    val solver = org.sat4j.pb.SolverFactory.newDefaultOptimizer()
    val res = try {
      val problem = new WDimacsReader( new WeightedMaxSatDecorator( solver ) ).parseInstance( new ByteArrayInputStream( sat4j_in.getBytes ) )
      readSat4j( problem, helper )
    } catch {
      case e: ContradictionException => None
    } finally {
      solver.reset
    }
    res
  }
}
