package gapt.formats.json.et

import gapt.proofs.expansion._
import gapt.proofs.lk.LKToExpansionProof
import org.specs2.mutable.Specification

class ExpansionProofCodecTest extends Specification {
  import gapt.formats.json.et.ExpansionTreeCodec._

  "The expansion proof de/serializer" should {
    "serialize and deserialize a small proof" in {
      val ep: ExpansionProof = LKToExpansionProof( gapt.examples.LinearExampleProof( 3 ) )
      val json = _expansionProofEncoder( ep )
      val epNew = _expansionProofDecoder.decodeJson( json )
      epNew must beRight( ep )
    }

    "serialize and deserialize a bigger proof" in {
      val ep: ExpansionProof = LKToExpansionProof( gapt.examples.theories.nat.add0l.combined() )
      val json = _expansionProofEncoder( ep )
      val epNew = _expansionProofDecoder.decodeJson( json )
      epNew must beRight( ep )
    }
  }
}