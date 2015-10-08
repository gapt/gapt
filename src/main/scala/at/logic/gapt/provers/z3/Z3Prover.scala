package at.logic.gapt.provers.z3

import java.io.IOException

import at.logic.gapt.formats.veriT.SmtLibExporter
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lkNew.LKProof
import at.logic.gapt.provers.{ renameConstantsToFi, Prover }
import at.logic.gapt.utils.traits.ExternalProgram
import at.logic.gapt.utils.{ runProcess, withTempFile }

class Z3Prover extends Prover with ExternalProgram {
  val nLine = sys.props( "line.separator" )
  val unsat = "unsat" + nLine
  val sat = "sat" + nLine

  override def isValid( seq: HOLSequent ): Boolean = {
    runProcess( Seq( "z3", "-smt2", "-in" ), SmtLibExporter( renameConstantsToFi( seq )._1 ) ) match {
      case `unsat` => true
      case `sat`   => false
    }
  }

  override def getLKProof( seq: HOLSequent ): Option[LKProof] =
    throw new UnsupportedOperationException

  override val isInstalled: Boolean =
    try {
      runProcess( Seq( "z3", "-version" ) )
      true
    } catch {
      case _: IOException => false
    }
}
