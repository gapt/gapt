package gapt.proofs.resolution

import gapt.expr._
import gapt.examples.{ BussTautology, CountingEquivalence }
import gapt.expr.fol.{ naive, thresholds }
import gapt.provers.escargot.Escargot
import org.specs2.mutable.Specification

class EliminateSplittingTest extends Specification {

  "example" in {
    val Some( proofWithSplitting ) = Escargot getResolutionProof hof"!x p x | !x q x -> !x (p x | q x) & ${BussTautology( 2 ).toImplication}"
    val proofWithoutSplitting = eliminateSplitting( proofWithSplitting )
    proofWithoutSplitting.subProofs foreach {
      case AvatarContradiction( _ ) => ko
      case AvatarComponent( _ )     => ko
      case AvatarSplit( _, _, _ )   => ko
      case _                        => ok
    }
    proofWithoutSplitting.isProof must_== true
  }

  "counting" in {
    val Some( proofWithSplitting ) = Escargot getResolutionProof CountingEquivalence( 3 )
    val proofWithoutSplitting = eliminateSplitting( proofWithSplitting )
    proofWithoutSplitting.isProof must_== true
  }

}
