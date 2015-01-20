import java.io._
import scala.io.Source
import scala.collection.immutable.HashMap
import org.slf4j.LoggerFactory

import at.logic.utils.executionModels.timeout._
import at.logic.calculi.expansionTrees.{ExpansionTree,ExpansionSequent,removeFromExpansionSequent}
import at.logic.algorithms.cutIntroduction._
import at.logic.algorithms.lk._
import at.logic.provers.eqProver._
import at.logic.provers._
import at.logic.transformations.herbrandExtraction.extractExpansionTrees

// for testCutIntro.compressProofSequences
:load examples/ProofSequences.scala

/**********
 * test script for the cut-introduction algorithm on output proofs from prover9,
 * veriT and example proof sequences.
 * usage example from CLI:
 *
 * scala> :load testing/testCutIntro.scala
 *
 * scala> testCutIntro.findNonTrivialTSTPExamples( "testing/TSTP/prover9/", 60 )
 *
 * test the tests by
 * scala> testCutIntro.compressTSTP ("testing/resultsCutIntro/tstp_minitest.csv", timeout: Int, method: Int)
 * scala> testCutIntro.compressVeriT ("testing/veriT-SMT-LIB/QF_UF/eq_diamond/", timeout: Int, method: Int)
 * scala> testCutIntro.compressProofSequences (timeout: Int, method: Int)
 * Where method is:
 * 0: introduce one cut with one quantifier
 * 1: introduce one cut with as many quantifiers as possible
 * 2: introduce many cuts with one quantifier each
 *
 * run the tests by
 * scala> testCutIntro.compressAll(timeout: Int)
 * see compressAll for how to call specific tests
 **********/

val CutIntroDataLogger = LoggerFactory.getLogger("CutIntroDataLogger")

/*
 * Each log line is a tuple consisting in the following values in this order:
 * 
 * name of the proof or file
 * description of the status of the operation
 * number of rules in the LK proof
 * number of quantifier rules in the LK proof
 * number of rules in the proof with cut
 * number of quantifier rules in the proof with cut
 * size of the term-set extracted
 * size of the minimal grammar found
 * number of minimal grammars
 * size of the canonical solution (logical complexity)
 * size of the minimized solution (logical complexity)
 * time for extracting the term set
 * time for generating the delta-table (when applicable)
 * time for finding the grammar (this includes the the time for generating the delta-table)
 * time for improving the solution
 * time for building the proof
 * time for cleaning the structural rules of the final proof
 * -------------
 * For general information about the logger, see the 'Guidelines'-page of the developer wiki.
 * For using the abover loggers, add (for example) the following to your log4j.xml:
 * 
 * <appender name="CutIntroDataLogFile" class="org.apache.log4j.FileAppender">
 *   <param name="File" value="logs/CutIntroDataLog.txt"/>
 *   <layout class="org.apache.log4j.PatternLayout">
 *     <param name="ConversionPattern" value="%m%n"/>
 *   </layout>
 * </appender>
 *
 * <logger name="CutIntroDataLogger">
 *   <level value="trace"/>
 *   <appender-ref ref="CutIntroDataLogFile"/>
 * </logger>
 *
 */

object testCutIntro {

  def apply() = {
    println("Usage: for example calls please see the implementation of testCutIntro.compressAll()")
  }

  def compressAll (timeout: Int) = {
    // note: the "now starting" - lines are logged in the data file so that it can be separated into the particular test runs later

    /*CutIntroDataLogger.trace( "---------- now starting ProofSeq/1 cut, 1 quantifier" )
    compressProofSequences (timeout, 0)
    CutIntroDataLogger.trace( "---------- now starting ProofSeq/1 cut, many quantifiers" )
    compressProofSequences (timeout, 1)
    CutIntroDataLogger.trace( "---------- now starting ProofSeq/many cuts, 1 quantifier" )
    compressProofSequences (timeout, 2)
*/
    CutIntroDataLogger.trace( "---------- now starting TSTP-Prover9/1 cut, 1 quantifier" )
    compressTSTP ("testing/resultsCutIntro/tstp_non_trivial_termset.csv", timeout, 0)
    CutIntroDataLogger.trace( "---------- now starting TSTP-Prover9/1 cut, many quantifiers" )
    compressTSTP ("testing/resultsCutIntro/tstp_non_trivial_termset.csv", timeout, 1)
    CutIntroDataLogger.trace( "---------- now starting TSTP-Prover9/many cuts, 1 quantifier" )
    compressTSTP ("testing/resultsCutIntro/tstp_non_trivial_termset.csv", timeout, 2)
    
    CutIntroDataLogger.trace( "---------- now starting SMT-LIB-QF_UF-veriT/1 cut, 1 quantifier" )
    compressVeriT ("testing/veriT-SMT-LIB/QF_UF/", timeout, 0)
    CutIntroDataLogger.trace( "---------- now starting SMT-LIB-QF_UF-veriT/1 cut, many quantifiers" )
    compressVeriT ("testing/veriT-SMT-LIB/QF_UF/", timeout, 1)
    CutIntroDataLogger.trace( "---------- now starting SMT-LIB-QF_UF-veriT/many cuts, 1 quantifier" )
    compressVeriT ("testing/veriT-SMT-LIB/QF_UF/", timeout, 2)
  }

  /*
   * Everything eventually ends up in one of these two methods.
   * All calls to cut-introduction and logging are done exclusively here
   *
   */
  def compressLKProof (proof: Option[LKProof], timeout: Int, method: Int, name: String, status: String) =
  status match {
    case "ok" =>
      val (cut_intro_status, info_tuple) = method match {
        case 0 => CutIntroduction.one_cut_one_quantifier_stat (proof.get, timeout)
        case 1 => CutIntroduction.one_cut_many_quantifiers_stat (proof.get, timeout)
        case 2 => CutIntroduction.many_cuts_one_quantifier_stat (proof.get, timeout)
      }
      val log_string = info_tuple.productIterator.foldLeft("") ( (acc, i) => acc + "," + i)  
      CutIntroDataLogger.trace(name + "," + cut_intro_status + log_string )
      cut_intro_status.split ("_").last
    case _ =>
      // Failed already during parsing, logging
      CutIntroDataLogger.trace(name + "," + status + ", , , , , , , , , , , , , , , " )
      status.split ("_").last
  }

  def compressExpansionProof (ep: Option[ExpansionSequent], hasEquality: Boolean, timeout: Int, method: Int, name: String, status: String) = 
  status match {
    case "ok" =>
      val (cut_intro_status, info_tuple) = method match {
        case 0 => CutIntroduction.one_cut_one_quantifier_stat (ep.get, hasEquality, timeout)
        case 1 => CutIntroduction.one_cut_many_quantifiers_stat (ep.get, hasEquality, timeout)
        case 2 => CutIntroduction.many_cuts_one_quantifier_stat (ep.get, hasEquality, timeout)
      }
      val log_string = info_tuple.productIterator.foldLeft("") ( (acc, i) => acc + "," + i)  
      CutIntroDataLogger.trace(name + "," + cut_intro_status + log_string )
    case _ =>
      // Failed already during parsing, logging
      CutIntroDataLogger.trace(name + "," + status + ", , , , , , , , , , , , , , , " )
  }

  /************** finding non-trival prover9-TSTP proofs **********************/

  var total = 0
  var num_trivial_termset = 0
  var error_parser = 0
  var error_term_extraction = 0
  // Hashmap containing proofs with non-trivial termsets
  var termsets = HashMap[String, TermSet]()

  def findNonTrivialTSTPExamples ( str : String, timeout : Int ) = {
    
    nonTrivialTermset(str, timeout)
    val file = new File("testing/resultsCutIntro/tstp_non_trivial_termset.csv")
    val summary = new File("testing/resultsCutIntro/tstp_non_trivial_summary.txt")
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
        val tssize = v.set.size
        val n_functions = v.formulaFunction.size
        instance_per_formula += tssize.toFloat/n_functions.toFloat
        ts_size += tssize
        k + "," + n_functions + "," + tssize + "\n" + acc
    }

    val avg_inst_per_form = instance_per_formula/termsets.size
    val avg_ts_size = ts_size.toFloat/termsets.size.toFloat

    bw.write(data)
    bw.close()

    bw_s.write("Total number of proofs: " + total + "\n")
    bw_s.write("Total number of proofs with trivial termsets: " + num_trivial_termset + "\n")
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
      try { withTimeout(timeout * 1000) { loadProver9LKProof(file.getAbsolutePath) match {
        case p: LKProof => try { withTimeout(timeout * 1000) { 
          val ts = extractTerms(p)
          val tssize = ts.set.size
          val n_functions = ts.formulaFunction.size

          if(tssize > n_functions)
            termsets += (file.getAbsolutePath -> ts)
          else num_trivial_termset += 1

        } } catch {
            case e: Throwable => error_term_extraction += 1
          }

      } } } catch {
	case e: Throwable => error_parser += 1
      }
    }
  }

  // Compress the prover9-TSTP proofs whose names are in the csv-file passed as parameter str
  def compressTSTP (str: String, timeout: Int, method: Int) = {
    
    // Process each file in parallel
    val lines = Source.fromFile(str).getLines().toList
    lines.par.foreach { case l =>
      val data = l.split(",")
      println ("*** Prover9 file: " + data(0))
      compressTSTPProof (data(0), timeout, method)
    }
  }

  /// compress the prover9-TSTP proof found in file fn
  def compressTSTPProof (fn: String, timeout: Int, method: Int) = {
    var status = "ok"

    val file = new File (fn)
    if (file.getName.endsWith(".out")) {
      val proof = try { withTimeout( timeout * 1000 ) {
        val p = loadProver9LKProof( file.getAbsolutePath )
        Some (p)
      } } catch {
        case e: TimeOutException =>
          status = "parsing_timeout"
          None
        case e: OutOfMemoryError =>
          status = "parsing_out_of_memory"
          None
        case e: StackOverflowError =>
          status = "parsing_stack_overflow"
          None
        case e: Exception =>
          status = "parsing_other_exception"
          None
      }

      compressLKProof (proof, timeout, method, fn, status)
    }
  }

  /****************************** VeriT SMT-LIB ******************************/

  // Compress all veriT-proofs found in the directory str and beyond
  def compressVeriT (str: String, timeout: Int, method: Int) = {
    val proofs = getVeriTProofs (str)
    proofs.par.foreach { case p => 
      println ("*** VeriT file: " + p)
      compressVeriTProof (p, timeout, method)
    }
  }

  def getVeriTProofs (str: String): List[String] = {
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

  // Compress the veriT-proof in file str
  def compressVeriTProof (str: String, timeout: Int, method: Int) {
    var status = "ok"

    val expproof = try { withTimeout( timeout * 1000 ) {
      val ep = loadVeriTProof (str)

      if ( ep.isEmpty ) {
        status = "parsing_no_proof_found"
      }

      ep
    } } catch {
      case e: TimeOutException =>
        status = "parsing_timeout"
        None
      case e: OutOfMemoryError =>
        status = "parsing_out_of_memory"
        None
      case e: StackOverflowError => 
        status = "parsing_stack_overflow"
        None
      case e: Exception =>
        status = "parsing_other_exception"
        None
    }

    // VeriT proofs have the equality axioms as formulas in the end-sequent
    compressExpansionProof (expproof, false, timeout, method, str, status)
  }

  /***************************** Proof Sequences ******************************/

  def compressProofSequences (timeout: Int, method: Int) = {

    var i = 0
    var status = ""
    while ( status != "timeout" ) {
      i = i + 1
      val pn = "LinearExampleProof(" + i + ")"
      status = compressLKProof (Some (LinearExampleProof (i)), timeout, method, pn, "ok")
    }

    i = 0
    status = ""
    while ( status != "timeout" ) {
      i = i + 1
      val pn = "SquareDiagonalExampleProof(" + i + ")"
      status = compressLKProof (Some (SquareDiagonalExampleProof (i)), timeout, method, pn, "ok")
    }

    i = 0
    status = ""
    while ( status != "timeout" ) {
      i = i + 1
      val pn = "SquareEdgesExampleProof(" + i + ")"
      status = compressLKProof (Some (SquareEdgesExampleProof (i)), timeout, method, pn, "ok")
    }

    i = 0
    status = ""
    while ( status != "timeout" ) {
      i = i + 1
      val pn = "SquareEdges2DimExampleProof(" + i + ")"
      status = compressLKProof (Some (SquareEdges2DimExampleProof(i)), timeout, method, pn, "ok")
    }

    i = 0
    status = ""
    while ( status != "timeout" ) {
      i = i + 1
      val pn = "LinearEqExampleProof(" + i + ")"
      status = compressLKProof (Some (LinearEqExampleProof(i)), timeout, method, pn, "ok")
    }

    i = 0
    status = ""
    while ( status != "timeout" ) {
      i = i + 1
      val pn = "SumOfOnesF2ExampleProof(" + i + ")"
      status = compressLKProof (Some (SumOfOnesF2ExampleProof(i)), timeout, method, pn, "ok")
    }

    i = 0
    status = ""
    while ( status != "timeout" ) {
      i = i + 1
      val pn = "SumOfOnesFExampleProof(" + i + ")"
      status = compressLKProof (Some (SumOfOnesFExampleProof(i)), timeout, method, pn, "ok")
    }

    i = 0
    status = ""
    while ( status != "timeout" ) {
      i = i + 1
      val pn = "SumOfOnesExampleProof(" + i + ")"
      status = compressLKProof (Some (SumOfOnesExampleProof(i)), timeout, method, pn, "ok")
    }

    i = 0
    status = ""
    while ( status != "timeout" ) {
      i = i + 1
      val pn = "UniformAssociativity3ExampleProof(" + i + ")"
      status = compressLKProof (Some (UniformAssociativity3ExampleProof(i)), timeout, method, pn, "ok")
    }
  }

/*
  def compressLKProof( name: String, p: LKProof, timeout: Int, moduloEq: Boolean, useForgetfulPara: Boolean ) = {
    val r = if ( moduloEq )
      compressExpansionProof( removeEqAxioms( extractExpansionTrees( p )), new EquationalProver(), timeout, useForgetfulPara )
    else
      compressExpansionProof( extractExpansionTrees( p ), new DefaultProver(), timeout, false )

    val status = r._1
    val cutintro_logline = r._2

    CutIntroDataLogger.trace( name + ",n/a," + status + ",n/a," + rulesNumber( p ) + "," + quantRulesNumber( p ) + cutintro_logline ) // log all, computing #infqf, #qinfcf
  }

  def removeEqAxioms( eseq: ExpansionSequent ) = {
   // removes all equality axioms that appear in examples/ProofSequences.scala
   val R = parse.fol( "Forall x =(x,x)" )
   val S = parse.fol( "Forall x Forall y Imp =(x,y) =(y,x)" )
   val T = parse.fol( "Forall x Forall y Forall z Imp And =(x,y) =(y,z) =(x,z)" )
   val Tprime = parse.fol( "Forall x Forall y Forall z Imp =(x,y) Imp =(y,z) =(x,z)" )
   val CSuc = parse.fol( "Forall x Forall y Imp =(x,y) =(s(x),s(y))" )
   val CPlus = parse.fol( "Forall x Forall y Forall u Forall v Imp =(x,y) Imp =(u,v) =(+(x,u),+(y,v))" )
   val CPlusL = parse.fol( "Forall x Forall y Forall z Imp =(y,z) =(+(y,x),+(z,x))" ) // congruence plus left
   val CgR = parse.fol( "Forall x Forall y Forall z Imp =(y,z) =(g(x,y),g(x,z))" ) // congruence of g on the right
   val CMultR = parse.fol( "Forall x Forall y Forall z Imp =(x,y) =(*(z,x),*(z,y))" ) // congruence of mult right

   val eqaxioms = new FSequent( R::S::T::Tprime::CSuc::CPlus::CPlusL::CgR::CMultR::Nil, Nil )
   
   removeFromExpansionSequent( eseq, eqaxioms )
  }
*/


}
