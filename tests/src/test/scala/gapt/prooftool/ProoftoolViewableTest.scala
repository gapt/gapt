package gapt.prooftool

import gapt.formats.llk.ExtendedProofDatabase
import gapt.proofs.HOLSequent
import gapt.proofs.ceres.Struct
import gapt.proofs.expansion.ExpansionProof
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.resolution.ResolutionProof
import gapt.proofs.sketch.RefutationSketch
import org.specs2.mutable.Specification

class ProoftoolViewableTest extends Specification {

  "implicit instances" in {
    implicitly[ProoftoolViewable[LKProof]]
    implicitly[ProoftoolViewable[ResolutionProof]]
    implicitly[ProoftoolViewable[RefutationSketch]]
    implicitly[ProoftoolViewable[ImpRightRule]]

    def forall[Viewable: ProoftoolViewable, Error] = {
      implicitly[ProoftoolViewable[Option[Viewable]]]
      implicitly[ProoftoolViewable[Either[Error, Viewable]]]
    }

    implicitly[ProoftoolViewable[ExpansionProof]]

    implicitly[ProoftoolViewable[Iterable[HOLSequent]]]
    implicitly[ProoftoolViewable[Seq[HOLSequent]]]
    implicitly[ProoftoolViewable[HOLSequent]]
    implicitly[ProoftoolViewable[ExtendedProofDatabase]]

    implicitly[ProoftoolViewable[Struct]]

    ok
  }

}
