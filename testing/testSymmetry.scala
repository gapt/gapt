import java.io._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle
import at.logic.gapt.formats.veriT.VeriTParser
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.expansionTrees.{compressQuantifiers, minimalExpansionSequent, getStatistics, removeFromExpansionSequent}
import org.slf4j.LoggerFactory

/**********
 * Test script for assessing redundancy in symmetry-instances of veriT-import.
 *
 * :load testing/testSymmetry.scala
 * gapt> testSymmetry.testSizes( "testing/veriT-SMT-LIB/QF_UF" )
 * gapt> testSymmetry.testMinimization( "testing/veriT-SMT-LIB/QF_UF" )
 *
 * Suggested logger-configuration:
 *
 * <appender name="TestSymmetryDataLogFile" class="org.apache.log4j.FileAppender">
 *   <param name="File" value="logs/TestSymmetryDataLog.txt"/>
 *   <layout class="org.apache.log4j.PatternLayout">
 *     <param name="ConversionPattern" value="%m%n"/>
 *   </layout>
 * </appender>
 *
 * <logger name="TestSymmetryDataLogger">
 *   <level value="trace"/>
 *   <appender-ref ref="TestSymmetryDataLogFile"/>
 * </logger>
 *
 */

val TestSymmetryDataLogger = LoggerFactory.getLogger("TestSymmetryDataLogger")

object testSymmetry {
  /**
   * For each ExpansionSequent obtained from veriT-import we compute one minimal
   * valid ExpansionSequent and print comparison of number of symmetry-instances.
   **/
  def testMinimization( str: String ) = {
    val minisat = new at.logic.gapt.provers.minisat.MiniSATProver
    val symm = Prover9TermParserLadrStyle.parseFormula( "( all x all y ( x = y -> y = x))" )
    TestSymmetryDataLogger.trace( "<filename>: <nsymm_import>, <nsymm_min>" )

    getVeriTProofs( str ).foreach { case fn =>
      val es = VeriTParser.getExpansionProofWithSymmetry( fn ).get
      val stats_import = getStatistics( compressQuantifiers( es ))
      val nsymm_import = if ( stats_import._1.contains( symm )) stats_import._1( symm ) else 0

      val min = minimalExpansionSequent( es, minisat ).get
      val stats_min = getStatistics( compressQuantifiers( min ))
      val nsymm_min = if ( stats_min._1.contains( symm )) stats_min._1( symm ) else 0

      TestSymmetryDataLogger.trace( fn + ": " + nsymm_import + ", " + nsymm_min )
    }
  }

  def testSizes( str: String ) = {
    val symm = Prover9TermParserLadrStyle.parseFormula( "( all x all y ( x = y -> y = x))" )
    TestSymmetryDataLogger.trace( "<filename>: <expseq_size>, <expseq_wosym_size>" )

    getVeriTProofs( str ).foreach { case fn =>
      val es = VeriTParser.getExpansionProofWithSymmetry( fn ).get
      val es_wosym = removeFromExpansionSequent( es, Sequent( symm::Nil, Nil ))
      val stats_import = getStatistics( compressQuantifiers( es ))
      val stats_wosym = getStatistics( compressQuantifiers( es_wosym ))
      TestSymmetryDataLogger.trace( fn + ": " + stats_import.total + ", " + stats_wosym.total )
    }
  }

  private def getVeriTProofs( str: String ): List[String] = {
    val file = new File (str)
    if (file.isDirectory) {
      val children = file.listFiles
      children.foldLeft(List[String]()) ((acc, f) => acc ::: getVeriTProofs (f.getPath))
    }
    else if (file.getName.endsWith(".proof_flat")) {
      List(file.getPath)
    }
    else List()
  }
}
