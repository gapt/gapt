package at.logic.gapt.provers.z3

import java.io.IOException

import at.logic.gapt.formats.veriT.SmtLibExporter
import at.logic.gapt.proofs.lk.base.{ LKProof, HOLSequent }
import at.logic.gapt.provers.Prover
import at.logic.gapt.utils.traits.ExternalProgram
import at.logic.gapt.utils.withTempFile

import scala.sys.process._

class Z3Prover extends Prover with ExternalProgram {
  override def isValid( seq: HOLSequent ): Boolean = {
    withTempFile.fromString( SmtLibExporter( seq ) ) { input =>
      Seq( "z3", "-smt2", input ) !!
    } match {
      case "unsat\n" => true
      case "sat\n"   => false
    }
  }

  override def getLKProof( seq: HOLSequent ): Option[LKProof] =
    throw new UnsupportedOperationException

  override val isInstalled: Boolean =
    try {
      Seq( "z3", "-version" ).!!
      true
    } catch {
      case _: IOException => false
    }
}
