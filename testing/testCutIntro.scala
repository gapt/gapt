import java.io._
import scala.io.Source
import scala.collection.immutable.HashMap
import org.slf4j.LoggerFactory

/**********
 * test script for the cut-introduction algorithm on output proofs from prover9,
 * usage example from CLI:
 *
 * scala> :load ../testing/testCutIntro.scala
 * scala> testCutIntro.findNonTrivialTSTPExamples( "../testing/prover9-TSTP/", 60 )
 * scala> testCutIntro.compressTSTP( "../testing/resultsCutIntro/tstp_non_trivial_termset.csv", 60 )
 * scala> testCutIntro.compressVeriT("../testing/veriT-SMT-LIB/QF_UF/", 300)
 **********/

val TestCutIntroLogger = LoggerFactory.getLogger("TestCutIntroLogger$")

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
  }

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

  // Compress the proofs that are in the csv file passed as a parameter
  def compressTSTP(str: String, timeout: Int) = {
    
    TestCutIntroLogger.trace("================ Compressing non-trivial TSTP examples ===============")
    
    var number = 0

    // Process each file
    val lines = Source.fromFile(str).getLines().toList
    lines.foreach{ case l =>
      number += 1
      val data = l.split(",")
      TestCutIntroLogger.trace("Processing proof number: " + number)
      compressProof(data(0), timeout)
    }
   
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

  }
  def compressProof(str: String, timeout: Int) = {
    TestCutIntroLogger.trace("FILE: " + str)
    val file = new File(str.trim)
    if (file.getName.endsWith(".out")) {
      total += 1
      runWithTimeout(timeout * 1000){ loadProver9LKProof(file.getAbsolutePath) } match {
        case Some(p) => 
          runWithTimeout(timeout * 1000){ 
            try { cutIntro2(p) } 
            catch { 
              case e: OutOfMemoryError => 
                out_of_memory += 1
                TestCutIntroLogger.trace("OutOfMemory: " + e)
                throw new Exception("OutOfMemory")
              case e: StackOverflowError => 
                stack_overflow += 1
                TestCutIntroLogger.trace("StackOverflow: " + e)
                throw new Exception("StackOverflow")
              case e: Exception => 
                error_cut_intro += 1
                TestCutIntroLogger.trace("Other exception: " + e)
                throw new Exception("OtherException")
            }
          } match {
            case Some(p_cut) =>
              try {
                val i1 = quantRulesNumber(p)
                val i2 = rulesNumber(p)
                val i3 = quantRulesNumber(p_cut)
                val i4 = rulesNumber(p_cut)
                finished += 1
                rulesInfo += (str -> ( i1, i2, i3, i4 )) 
              } catch {
                case e: Exception => 
                  error_rule_count += 1
                  TestCutIntroLogger.trace("Error in rule count: " + e)
                  throw new Exception("Error in rule count")
              }
            case None => ()
          }
        case None => 
          TestCutIntroLogger.trace("Error in parsing.")
          error_parser += 1
      }
    }
  }

  def compressVeriT( str : String, timeout : Int) = {

    TestCutIntroLogger.trace("================ Compressing VeriT proofs ===============")
    
    processVeriT(str, timeout)
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

  }
  def processVeriT(str: String, timeout: Int) : Unit = {
    val file = new File(str)
    if (file.isDirectory) {
      val children = file.listFiles
      children.foreach(f => processVeriT(f.getAbsolutePath, timeout))
    }
    else if (file.getName.endsWith(".proof_flat")) {
      total += 1
      TestCutIntroLogger.trace("FILE: " + file.getAbsolutePath)
      runWithTimeout(timeout * 1000){ 
        try { loadVeriTProof(file.getAbsolutePath) }
        catch {
          case e: OutOfMemoryError =>
            error_parser_OOM += 1
            TestCutIntroLogger.trace("OutOfMemory (parsing): " + e)
            throw new Exception("OutOfMemory")              
          case e: StackOverflowError => 
            error_parser_SO += 1
            TestCutIntroLogger.trace("StackOverflow (parsing): " + e)
            throw new Exception("StackOverflow")
          case e: Exception =>
            error_parser_other += 1
            TestCutIntroLogger.trace("Other exception (parsing): " + e)
            throw new Exception("OtherException (TLE?)")
        }
      } match {
        case Some(p) => 
          runWithTimeout(timeout * 1000){ 
            try { cutIntro2(p) } 
            catch { 
              case e: OutOfMemoryError => 
                out_of_memory += 1
                TestCutIntroLogger.trace("OutOfMemory (cut-intro): " + e)
                throw new Exception("OutOfMemory")
              case e: StackOverflowError => 
                stack_overflow += 1
                TestCutIntroLogger.trace("StackOverflow (cut-intro): " + e)
                throw new Exception("StackOverflow")
              case e: Exception =>
                error_cut_intro += 1
                TestCutIntroLogger.trace("Other exception (cut-intro): " + e)
                throw new Exception("OtherException (not compressable? TLE?)")
            }
          } match {
            case Some(with_cut) =>
              try {
                val i1 = at.logic.calculi.expansionTrees.quantRulesNumber(p)
                //val i2 = rulesNumber(p)
                val i3 = quantRulesNumber(with_cut)
                val i4 = rulesNumber(with_cut)
                finished += 1
                rulesInfo += (str -> ( i1, 0, i3, i4 )) 
              } catch {
                case e: Exception => 
                  error_rule_count += 1
                  TestCutIntroLogger.trace("Error in rule count: " + e)
                  throw new Exception("Error in rule count")
              }
            case None => ()
          }
        case None => () 
      }
    } 
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

