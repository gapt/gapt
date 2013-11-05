import java.io._
import scala.io.Source
import scala.collection.immutable.HashMap
import org.slf4j.LoggerFactory

import at.logic.calculi.expansionTrees.ExpansionTree
import at.logic.algorithms.cutIntroduction.{CutIntroduction,CutIntroUncompressibleException,CutIntroEHSUnprovableException}

/**********
 * test script for the cut-introduction algorithm on output proofs from prover9,
 * veriT and example proof sequences.
 * usage example from CLI:
 *
 * scala> :load ../testing/testCutIntro.scala
 * scala> testCutIntro.findNonTrivialTSTPExamples( "../testing/prover9-TSTP/", 60 )
 * scala> testCutIntro.compressTSTP( "../testing/resultsCutIntro/tstp_non_trivial_termset.csv", 60 )
 * scala> testCutIntro.compressVeriT( "../testing/veriT-SMT-LIB/QF_UF/", 60 )
 * scala> testCutIntro.compressProofSequences( 60 )
 **********/

val TestCutIntroLogger = LoggerFactory.getLogger("TestCutIntroLogger$")
val CutIntroDataLogger = LoggerFactory.getLogger("CutIntroDataLogger$")

class TimeOutException extends Exception

// for testCutIntro.compressProofSequences
:load ../examples/ProofSequences.scala


object testCutIntro {
  var total = 0
  var error_parser = 0
  var error_parser_OOM = 0
  var error_parser_SO = 0
  var error_parser_other = 0
  var error_term_extraction = 0
  var error_cut_intro = 0
  var out_of_memory = 0
  var stack_overflow = 0
  var error_rule_count = 0
  var finished = 0
  // Hashmap containing proofs with non-trivial termsets
  var termsets = HashMap[String, FlatTermSet]()
  // File name -> q-rules before cut, rules before cut, q-rules after
  // cut, rules after cut
  var rulesInfo = HashMap[String, (Int, Int, Int, Int)]()

  def apply() = {
    println("Usage:")
    println()
    println("Finds all proofs with non trivial term-sets. " + 
      "Prints the results to resultsCutIntro/tstp_non_trivial_termset.csv and resultsCutIntro/tstp_non_trivial_summary.txt")
    println("scala> testCutIntro.findNonTrivialTSTPExamples( \"../testing/prover9-TSTP/\", 60 )")
    println()
    println("Compress the proofs of the TSTP library in the file tstp_non_trivial_termset.csv. " + 
      "The proofs that could be compressed are in resultsCutIntro/pleaseChangeToTheRightRevisionNumber/tstp_compressed.csv and a " + 
      "summary of the operations is in resultsCutIntro/pleaseChangeToTheRightRevisionNumber/tstp_compressed_summary.txt")
    println("scala> testCutIntro.compressTSTP( \"../testing/resultsCutIntro/tstp_non_trivial_termset.csv\", 60 )")
    println()
    println("Parses and compress the proofs from the VeriT library. " + 
      "The results are in resultsCutIntro/pleaseChangeToTheRightRevisionNumber/verit_compressed.csv and resultsCutIntro/pleaseChangeToTheRightRevisionNumber/verit_compressed_summary.txt")
    println("scala> testCutIntro.compressVeriT(\"../testing/veriT-SMT-LIB/QF_UF/\", 60)")
    println()
    println("Compress proofs from ../examples/ProofSequences.scala")
    println("scala> testCutIntro.compressProofSequences(60)")
  }

  /************** finding non-trival prover9-TSTP proofs **********************/

  def findNonTrivialTSTPExamples ( str : String, timeout : Int) = {
    
    TestCutIntroLogger.trace("================ Finding TSTP non-trivial examples ===============")

    nonTrivialTermset(str, timeout)
    val file = new File("../testing/resultsCutIntro/tstp_non_trivial_termset.csv")
    val summary = new File("../testing/resultsCutIntro/tstp_non_trivial_summary.txt")
    file.createNewFile()
    summary.createNewFile()
    val fw = new FileWriter(file.getAbsoluteFile)
    val bw = new BufferedWriter(fw)
    val fw_s = new FileWriter(summary.getAbsoluteFile)
    val bw_s = new BufferedWriter(fw_s)

    var instance_per_formula = 0.0
    var ts_size = 0
    val data = termsets.foldLeft("") {
      case (acc, (k, v)) =>
        val tssize = v.termset.size
        val n_functions = v.formulaFunction.size
        instance_per_formula += tssize.toFloat/n_functions.toFloat
        ts_size += tssize
        k + " , " + n_functions + " , " + tssize + "\n" + acc
    }

    val avg_inst_per_form = instance_per_formula/termsets.size
    val avg_ts_size = ts_size.toFloat/termsets.size.toFloat

    bw.write(data)
    bw.close()

    bw_s.write("Total number of proofs: " + total + "\n")
    bw_s.write("Total number of proofs with non-trivial termsets: " + termsets.size + "\n")
    bw_s.write("Time limit exceeded or exception during parsing: " + error_parser + "\n")
    bw_s.write("Time limit exceeded or exception during terms extraction: " + error_term_extraction + "\n")
    bw_s.write("Average instances per quantified formula: " + avg_inst_per_form + "\n")
    bw_s.write("Average termset size: " + avg_ts_size + "\n")
    bw_s.close()

  }
  def nonTrivialTermset(str : String, timeout : Int) : Unit = {
    val file = new File(str)
    if (file.isDirectory) {
      val children = file.listFiles
      children.foreach(f => nonTrivialTermset(f.getAbsolutePath, timeout))
    }
    else if (file.getName.endsWith(".out")) {
      total += 1
      TestCutIntroLogger.trace("\nFILE: " + file.getAbsolutePath)
      runWithTimeout(timeout * 1000){ loadProver9LKProof(file.getAbsolutePath) } match {
        case Some(p) => 
          runWithTimeout(timeout * 1000){ 
            val ts = extractTerms(p)
            val tssize = ts.termset.size
            val n_functions = ts.formulaFunction.size
            if(tssize > n_functions) {
              termsets += (file.getAbsolutePath -> ts)
              tssize
            }
            else 0
            //cutIntro(p) 
          } match {
            case Some(n) =>
              if(n > 0) {
                TestCutIntroLogger.trace("File: " + file.getAbsolutePath + " has term-set of size " + n)
              }
            case None => error_term_extraction += 1
          }
        case None => error_parser += 1
      }
    }       
  }

  // Compress the prover9-TSTP proofs whose names are in the csv-file passed as parameter str
  def compressTSTP( str: String, timeout: Int ) = {
    
    TestCutIntroLogger.trace("================ Compressing non-trivial TSTP examples ===============")
    
    var number = 0

    // Process each file
    val lines = Source.fromFile(str).getLines().toList
    lines.foreach{ case l =>
      number += 1
      val data = l.split(",")
      TestCutIntroLogger.trace("Processing proof number: " + number)
      compressTSTPProof(data(0), timeout)
    }
   
/* old stats output
    // Write results
    val file = new File("../testing/resultsCutIntro/pleaseChangeToTheRightRevisionNumber/tstp_compressed.csv")
    val summary = new File("../testing/resultsCutIntro/pleaseChangeToTheRightRevisionNumber/tstp_compressed_summary.txt")
    file.createNewFile()
    summary.createNewFile()
    val fw = new FileWriter(file.getAbsoluteFile)
    val bw = new BufferedWriter(fw)
    val fw_s = new FileWriter(summary.getAbsoluteFile)
    val bw_s = new BufferedWriter(fw_s)

    var compression_rate_quant = 0.0
    var compression_rate = 0.0
    val data = rulesInfo.foldLeft("") {
      case (acc, (k, v)) =>
        val q_before = v._1
        val tot_before = v._2
        val q_after = v._3
        val tot_after = v._4
        
        compression_rate_quant += q_after/q_before
        compression_rate += tot_after/tot_before

        k + " , " + q_before + " , " + tot_before + " , " + q_after + " , " + tot_after + "\n" + acc
    }

    val avg_compression_quant = compression_rate_quant/rulesInfo.size
    val avg_compression = compression_rate/rulesInfo.size.toFloat

    bw.write("# File name, quant. cut-free, infer. cut-free, quant. with cut, infer. with cut \n")
    bw.write(data)
    bw.close()

    bw_s.write("Total number of proofs: " + lines.size + "\n")
    bw_s.write("Total number of proofs processed: " + total + "\n")
    bw_s.write("Total number of proofs compressed: " + finished + "\n")
    bw_s.write("Time limit exceeded or exception during parsing: " + error_parser + "\n")
    bw_s.write("Exception during cut-introduction: " + error_cut_intro + "\n")
    bw_s.write("Out of memory during cut-introduction: " + out_of_memory + "\n")
    bw_s.write("Stack overflow during cut-introduction: " + stack_overflow + "\n")
    bw_s.write("Error during rule counting: " + error_rule_count + "\n")
    bw_s.write("The rest of the proofs probably exceeded the time limit during cut-introduction.\n")
    bw_s.write("Average compression rate of quantifier rules: " + avg_compression_quant + "\n")
    bw_s.write("Average compression rate: " + avg_compression + "\n")
    bw_s.close()
*/
  }

  /// compress the prover9-TSTP proof found in file fn
  def compressTSTPProof( fn: String, timeout: Int ) = {
    var log_ptime_ninfcf_nqinfcf = ""
    var parsing_status = "ok"
    var cutintro_status = "ok"
    var cutintro_logline = ""

    TestCutIntroLogger.trace( "FILE: " + fn )

    val file = new File(fn.trim)
    if (file.getName.endsWith(".out")) {
      val expproof = try { withTimeout( timeout * 1000 ) {
        val t0 = System.currentTimeMillis
        val p = loadProver9LKProof( file.getAbsolutePath )
        val ep = extractExpansionTrees( p )
        val t1 = System.currentTimeMillis
        
        log_ptime_ninfcf_nqinfcf = ", " + (t1 - t0) + ", " + rulesNumber(p) + ", " + quantRulesNumber(p) // log ptime, #infcf, #qinfcf

        Some(ep)
      } } catch {
        case e: TimeOutException =>
          TestCutIntroLogger.trace("Parsing: Timeout")
          parsing_status = "parsing_timeout"
          None
        case e: OutOfMemoryError =>
          TestCutIntroLogger.trace("Parsing: OutOfMemory: " + e)
          parsing_status = "parsing_out_of_memory"
          None
        case e: StackOverflowError =>
          TestCutIntroLogger.trace("Parsing: StackOverflow: " + e)
          parsing_status = "parsing_stack_overflow"
          None
        case e: Exception =>
          TestCutIntroLogger.trace("Parsing: Other exception: " + e)
          parsing_status = "parsing_other_exception"
          None
      }

      expproof match {
        case Some(ep) =>
          val r = compressExpansionProof( ep, timeout )
          cutintro_status = r._1
          cutintro_logline = r._2
        case None => ()
      }

      if ( parsing_status == "ok" ) {
        if ( cutintro_status == "ok" ) {
          CutIntroDataLogger.trace( fn + ", ok" + log_ptime_ninfcf_nqinfcf + cutintro_logline )
        }
        else {
          CutIntroDataLogger.trace( fn + ", " + cutintro_status )
        }
      }
      else {
        CutIntroDataLogger.trace( fn + ", " + parsing_status )
      }
    }
  }

  /****************************** VeriT SMT-LIB ******************************/

  /// compress all veriT-proof found recursively in the directory str
  def compressVeriT( str : String, timeout : Int ) = {
    TestCutIntroLogger.trace("================ Compressing VeriT proofs ===============")
    recCompressVeriT( str, timeout )
  }

  def recCompressVeriT( str : String, timeout : Int ): Unit = {
    val file = new File( str )
    if (file.isDirectory) {
      val children = file.listFiles
      children.foreach( f => recCompressVeriT( f.getPath, timeout ))
    }
    else if (file.getName.endsWith(".proof_flat")) {
      compressVeriTProof( file.getPath, timeout )
    }
  }

  /// compress the veriT-proof str
  def compressVeriTProof( str: String, timeout: Int ) {
    var parsing_status = "ok"
    var cutintro_status = "ok"
    var cutintro_logline = ""
    var log_ptime_ninfcf_nqinfcf = ""

    TestCutIntroLogger.trace("FILE: " + str)

    val expproof = try { withTimeout( timeout * 1000 ) {
      val t0 = System.currentTimeMillis
      val ep = loadVeriTProof( str )
      val t1 = System.currentTimeMillis

      log_ptime_ninfcf_nqinfcf = ", " + (t1 - t0) + ", n/a, n/a" // log ptime, #infcf, #qinfcf

      Some(ep)
    } } catch {
      case e: TimeOutException =>
        TestCutIntroLogger.trace("Parsing: Timeout")
        parsing_status = "parsing_timeout"
        None
      case e: OutOfMemoryError =>
        TestCutIntroLogger.trace("Parsing: OutOfMemory: " + e)
        parsing_status = "parsing_out_of_memory"
        None
      case e: StackOverflowError => 
        TestCutIntroLogger.trace("Parsing: StackOverflow: " + e)
        parsing_status = "parsing_stack_overflow"
        None
      case e: Exception =>
        TestCutIntroLogger.trace("Parsing: Other exception: " + e)
        parsing_status = "parsing_other_exception"
        None
    }

    expproof match {
      case Some(ep) =>
        val r = compressExpansionProof( ep, timeout )
        cutintro_status = r._1
        cutintro_logline = r._2
      case None => ()
    }

    if ( parsing_status == "ok" ) {
      if ( cutintro_status == "ok" ) {
        CutIntroDataLogger.trace( str + ", ok" + log_ptime_ninfcf_nqinfcf + cutintro_logline )
      }
      else {
        CutIntroDataLogger.trace( str + ", " + cutintro_status )
      }
    }
    else {
      CutIntroDataLogger.trace( str + ", " + parsing_status )
    }
  }

/* old stats output
    val file = new File("../testing/resultsCutIntro/pleaseChangeToTheRightRevisionNumber/verit_compressed.csv")
    val summary = new File("../testing/resultsCutIntro/pleaseChangeToTheRightRevisionNumber/verit_compressed_summary.txt")
    file.createNewFile()
    summary.createNewFile()
    val fw = new FileWriter(file.getAbsoluteFile)
    val bw = new BufferedWriter(fw)
    val fw_s = new FileWriter(summary.getAbsoluteFile)
    val bw_s = new BufferedWriter(fw_s)

    var compression_rate_quant = 0.0
    //var compression_rate = 0.0
    val data = rulesInfo.foldLeft("") {
      case (acc, (k, v)) =>
        val q_before = v._1
        //val tot_before = v._2
        val q_after = v._3
        val tot_after = v._4
        
        compression_rate_quant += q_after/q_before
        //compression_rate += tot_after/tot_before

        k + " , " + q_before + " , " + q_after + " , " + tot_after + "\n" + acc
    }

    val avg_compression_quant = compression_rate_quant/rulesInfo.size
    //val avg_compression = compression_rate/rulesInfo.size.toFloat

    bw.write("# File name, quant.cut-free, quant. with cut, infer. with cut \n")
    bw.write(data)
    bw.close()
    
    bw_s.write("Total number of proofs processed: " + total + "\n")
    bw_s.write("Total number of proofs compressed: " + finished + "\n\n")
    
    bw_s.write("Out of memory during parsing: " + error_parser_OOM + "\n")
    bw_s.write("Stack overflow during parsing: " + error_parser_SO + "\n")
    bw_s.write("Other exception during parsing: " + error_parser_other + "\n\n")
    
    bw_s.write("Out of memory during cut-introduction: " + out_of_memory + "\n")
    bw_s.write("Stack overflow during cut-introduction: " + stack_overflow + "\n")
    bw_s.write("Error during rule counting: " + error_rule_count + "\n")
    bw_s.write("Other exception during cut-introduction: " + error_cut_intro + "\n\n")

    bw_s.write("Average compression rate of quantifier rules: " + avg_compression_quant + "\n")
    //bw_s.write("Average compression rate: " + avg_compression + "\n")
    bw_s.close()
*/


  /***************************** Proof Sequences ******************************/

  def compressProofSequences( timeout: Int ) {
    TestCutIntroLogger.trace("================ Compressing proof sequences ===============")

    for ( i <- 1 to 12 ) {
      val pn = "LinearExampleProof(" + i + ")"
      TestCutIntroLogger.trace( "PROOF: " + pn )
      compressLKProof( pn, LinearExampleProof( i ), timeout )
    }

    for ( i <- 1 to 10 ) {
      val pn = "SquareDiagonalExampleProof(" + i + ")"
      TestCutIntroLogger.trace( "PROOF: " + pn )
      compressLKProof( pn, SquareDiagonalExampleProof( i ), timeout )
    }

    for ( i <- 1 to 8 ) {
      val pn = "SquareEdgesExampleProof(" + i + ")"
      TestCutIntroLogger.trace( "PROOF: " + pn )
      compressLKProof( pn, SquareEdgesExampleProof( i ), timeout )
    }

    for ( i <- 1 to 9 ) {
      val pn = "SquareEdges2DimExampleProof(" + i + ")"
      TestCutIntroLogger.trace( "PROOF: " + pn )
      compressLKProof( pn, SquareEdges2DimExampleProof( i ), timeout )
    }

    for ( i <- 1 to 10 ) {
      val pn = "LinearEqExampleProof(" + i + ")"
      TestCutIntroLogger.trace( "PROOF: " + pn )
      compressLKProof( pn, LinearEqExampleProof( i ), timeout )
    }

    for ( i <- 1 to 5 ) {
      val pn = "SumOfOnesF2ExampleProof(" + i + ")"
      TestCutIntroLogger.trace( "PROOF: " + pn )
      compressLKProof( pn, SumOfOnesF2ExampleProof( i ), timeout )
    }

    for ( i <- 1 to 5 ) {
      val pn = "SumOfOnesFExampleProof(" + i + ")"
      TestCutIntroLogger.trace( "PROOF: " + pn )
      compressLKProof( pn, SumOfOnesFExampleProof( i ), timeout )
    }

    for ( i <- 1 to 6 ) {
      val pn = "SumOfOnesExampleProof(" + i + ")"
      TestCutIntroLogger.trace( "PROOF: " + pn )
      compressLKProof( pn, SumOfOnesExampleProof( i ), timeout )
    }

    for ( i <- 1 to 2 ) {
      val pn = "UniformAssociativity3ExampleProof(" + i + ")"
      TestCutIntroLogger.trace( "PROOF: " + pn )
      compressLKProof( pn, UniformAssociativity3ExampleProof( i ), timeout )
    }

  }

  def compressLKProof( name: String, p: LKProof, timeout: Int ) = {
    val r = compressExpansionProof( extractExpansionTrees( p ), timeout )
    val cutintro_status = r._1
    val cutintro_logline = r._2

    if ( cutintro_status == "ok" ) {
      CutIntroDataLogger.trace( name + ", ok, n/a, " + rulesNumber( p ) + ", " + quantRulesNumber( p ) + cutintro_logline )
    }
    else {
      CutIntroDataLogger.trace( name + ", " + cutintro_status )
    }
  }


  /******************* auxiliary stuff for all test-suites ********************/

  /**
   * Runs experimental cut-introduction on the expansion proof ep. This is the
   * only call to cut-introduction in this test-script.
   *
   * @return ( status, logline )
   **/
  def compressExpansionProof( ep: (Seq[ExpansionTree],Seq[ExpansionTree]), timeout: Int ) : ( String, String ) = {
    var status = "ok"
    var logline = ""

    try { withTimeout( timeout * 1000 ) {
      logline = CutIntroduction.applyExp( ep )._2 // get logline and discard proof
    } } catch { 
      case e: TimeOutException =>
        TestCutIntroLogger.trace("Timeout")
        status = "cutintro_timeout"
      case e: OutOfMemoryError =>
        TestCutIntroLogger.trace("OutOfMemory: " + e)
        status = "cutintro_out_of_memory"
      case e: StackOverflowError =>
        TestCutIntroLogger.trace("StackOverflow: " + e)
        status = "cutintro_stack_overflow"
      case e: CutIntroUncompressibleException =>
        TestCutIntroLogger.trace("Input Uncompressible: " + e)
        status = "cutintro_uncompressible"
      case e: CutIntroEHSUnprovableException =>
        TestCutIntroLogger.trace("Extended Herbrand Sequent unprovable: " + e)
        status = "cutintro_ehs_unprovable"
      case e: Exception =>
        TestCutIntroLogger.trace("Other exception: " + e)
        status = "cutintro_other_exception"
    }

    ( status, logline )
  }

  /**
   * runs f with timeout to
   *
   * If f does terminate within to milliseconds returns its result. If not
   * throw a TimeOutException. If f throws an exception it is propagated to
   * the caller of withTimeout.
   *
   * Use this as follows:
   * try { withTimeout( 1234 ) {
   *   ... your code ...
   * } } catch {
   *   case toe: TimeOutException ...
   *   case ... other exception
   * }
   **/
  def withTimeout[T]( to: Long )( f: => T ) : T = {
    var result:Either[Throwable,T] = Left(new TimeOutException())

    val r = new Runnable {
      def run() {
        try {
          result = Right( f )
        } catch {
          case e: Exception =>
            result = Left(e)
        }
      }
    }

    val t = new Thread( r )
    t.start()
    t.join( to )
    if ( t.isAlive() ) {
      t.stop()
    }

    if ( result.isLeft ) throw result.left.get
    else result.right.get
  }





  /**
   * Run f
   *
   * If f terminates within to milliseconds return its result, if it throws an
   * exception or does not terminate within to milliseconds, return None.
   **/
  private def runWithTimeout[T >: Nothing]( to: Long )( f: => T ) : Option[T] = {
    var output:Option[T] = None

    val r = new Runnable { def run() { output = Some( f ) } }
    val t = new Thread( r )
    t.start()
    t.join( to )
    if ( t.isAlive() ) {
      TestCutIntroLogger.trace("TIMEOUT.")
      t.stop()
    }

    output
  }



}

