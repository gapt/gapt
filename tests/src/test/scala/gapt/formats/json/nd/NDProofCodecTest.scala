package gapt.formats.json.nd

import gapt.proofs.lk.LKToND
import gapt.proofs.nd.NDProof
import org.specs2.mutable.Specification

class NDProofCodecTest extends Specification {
  import gapt.formats.json.nd.NDProofCodec._

  "The ND proof de/serializer" should {
    "serialize and deserialize a small proof" in {
      val p: NDProof = LKToND( gapt.examples.LinearExampleProof( 3 ) )
      val json = _ndProofEncoder( p )
      val pNew = _ndProofDecoder.decodeJson( json )
      pNew must beRight( p )
    }

    "serialize and deserialize a bigger proof" in {
      val p: NDProof = LKToND( gapt.examples.theories.nat.add0l.combined() )
      val json = _ndProofEncoder( p )
      val pNew = _ndProofDecoder.decodeJson( json )
      pNew must beRight( p )
    }
  }
}