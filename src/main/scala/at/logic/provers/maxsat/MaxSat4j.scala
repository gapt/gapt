package at.logic.provers.maxsat

import java.io.{ File, BufferedWriter, FileWriter }

import at.logic.calculi.resolution.FClause
import at.logic.provers.sat4j.readSat4j
import org.sat4j.maxsat.reader.WDimacsReader
import org.sat4j.maxsat.WeightedMaxSatDecorator
import org.sat4j.pb.IPBSolver
import org.sat4j.specs.ContradictionException

/**
 * Created by frain on 4/1/15.
 */
class MaxSat4j extends MaxSATSolver {
  def solve( hard: List[FClause], soft: List[( FClause, Int )] ) = {
    val helper = new WDIMACSHelper( hard, soft )
    val sat4j_in = helper.getWCNFInput().toString()

    trace( "Generated Sat4j input: " )

    val temp_in = File.createTempFile( "gapt_sat4j_in", ".sat" )
    temp_in.deleteOnExit()

    val out = new BufferedWriter( new FileWriter( temp_in ) )
    out.append( sat4j_in )
    out.close()

    // run Sat4j

    debug( "Starting sat4j..." )
    val solver = org.sat4j.maxsat.SolverFactory.newDefault()
    val res = try {
      val problem = new WDimacsReader( new WeightedMaxSatDecorator( solver ) ).parseInstance( temp_in.getAbsolutePath )
      readSat4j( problem, helper )
    } catch {
      case e: ContradictionException => None
    } finally {
      solver.reset
    }
    res
  }
}
