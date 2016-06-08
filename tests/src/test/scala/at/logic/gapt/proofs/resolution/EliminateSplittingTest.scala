package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.examples.BussTautology
import at.logic.gapt.expr.fol.{ naive, thresholds }
import at.logic.gapt.provers.escargot.Escargot
import org.specs2.mutable.Specification

class EliminateSplittingTest extends Specification {

  "example" in {
    val Some( proofWithSplitting ) = Escargot getResolutionProof hof"!x p x | !x q x -> !x (p x | q x) & ${BussTautology( 2 ).toImplication}"
    val proofWithoutSplitting = eliminateSplitting( proofWithSplitting )
    proofWithoutSplitting.subProofs foreach {
      case AvatarAbsurd( _ )              => ko
      case AvatarComponentIntro( _ )      => ko
      case AvatarComponentElim( _, _, _ ) => ko
      case _                              => ok
    }
    proofWithoutSplitting.isProof must_== true
  }

  "counting" in {
    val Seq( x, y, z ) = Seq( "x", "y", "z" ) map { FOLVar( _ ) }
    val as = 0 to 3 map { i => All( x, Ex( y, FOLAtom( s"a$i", x, y, z ) ) ) }
    val formula = All( z, thresholds.exactly oneOf as ) <-> All( z, naive.exactly oneOf as )
    val Some( proofWithSplitting ) = Escargot getResolutionProof formula
    val proofWithoutSplitting = eliminateSplitting( proofWithSplitting )
    proofWithoutSplitting.isProof must_== true
  }

}
