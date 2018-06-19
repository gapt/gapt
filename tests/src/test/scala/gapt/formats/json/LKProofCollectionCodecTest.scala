package gapt.formats.json

import org.specs2.mutable.Specification
import io.circe.syntax._
import gapt.proofs.lk._

class LKProofCollectionCodecTest extends Specification {
  import LKProofCodec._

  "The LK collection de/serializer" should {
    "serialize and deserialize a small proof" in {
      val p: LKProof = gapt.examples.LinearExampleProof( 3 )
      val coll = ProofCollection( p )
      val json = coll.asJson
      val collNew = json.as[ProofCollection[LKProof]]
      collNew must beRight( coll )
    }

    "serialize and deserialize a bigger proof" in {
      val p: LKProof = gapt.examples.theories.nat.add0l.combined()
      val coll = ProofCollection( p )
      val json = coll.asJson
      val collNew = json.as[ProofCollection[LKProof]]
      collNew must beRight( coll )
    }
  }
}
