package gapt.formats.json.lk

import gapt.proofs.lk._
import org.specs2.mutable.Specification
import gapt.examples.sequence.LinearExampleProof

class LKProofCodecTest extends Specification {
  import gapt.formats.json.lk.LKProofCodec._

  "The LK proof de/serializer" should {
    "serialize and deserialize a small proof" in {
      val p: LKProof = LinearExampleProof(3)
      val json = _lkProofEncoder(p)
      val pNew = _lkProofDecoder.decodeJson(json)
      pNew must beRight(p)
    }

    "serialize and deserialize a bigger proof" in {
      val p: LKProof = gapt.examples.theories.nat.add0l.combined()
      val json = _lkProofEncoder(p)
      val pNew = _lkProofDecoder.decodeJson(json)
      pNew must beRight(p)
    }
  }
}
