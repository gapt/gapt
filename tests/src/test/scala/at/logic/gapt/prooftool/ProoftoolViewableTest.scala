package at.logic.gapt.prooftool

import at.logic.gapt.formats.llk.ExtendedProofDatabase
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.ceres.Struct
import at.logic.gapt.proofs.expansion.ExpansionProof
import at.logic.gapt.proofs.lk.{ ImpRightRule, LKProof }
import at.logic.gapt.proofs.resolution.ResolutionProof
import at.logic.gapt.proofs.sketch.RefutationSketch
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
