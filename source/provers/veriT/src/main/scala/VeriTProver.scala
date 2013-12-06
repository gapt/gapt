
package at.logic.provers.veriT

import scala.sys.process._
import java.io._
import at.logic.provers.Prover
import at.logic.parsing.veriT._
import at.logic.language.hol.HOLFormula
import at.logic.calculi.lk.base.types.FSequent

object VeriTProver extends Prover {

  override def isValid(s: FSequent) : Boolean = {

    // Generate the input file for veriT
    val in_file = VeriTExporter(s, "toProve.smt")

    // Execute the system command and get the result as a string.
    val result = try { "veriT --proof-version=1 --proof=- toProve.smt".!! }
    catch {
      case e: IOException => throw new Exception("VeriT is not installed.")
    }

    println("result: " + result)

    in_file.delete() match {
      case true => ()
      case false => throw new Exception("Error deleting smt file.")
    }

    val out_file = new File("proof.smt")
    val pw = new PrintWriter(out_file)
    pw.write(result)
    pw.close()

    // Parse the output
    val proof = VeriTParser.getExpansionProof(out_file.getAbsolutePath())
    out_file.delete() match {
      case true => ()
      case false => throw new Exception("Error deleting verit file.")
    }
    proof match {
      case Some(_) => true
      case None => false
    }
  }

  // VeriT proofs are parsed as Expansion Trees.
  // At the moment there is no method implemented that 
  // would generate an LK proof from an Expansion Tree.
  override def getLKProof(s: FSequent) = 
    throw new Exception("It is not possible to generate LK proofs from VeriT proofs at the moment.")
  override def getLKProof(f: HOLFormula) = 
    throw new Exception("It is not possible to generate LK proofs from VeriT proofs at the moment.")
}
