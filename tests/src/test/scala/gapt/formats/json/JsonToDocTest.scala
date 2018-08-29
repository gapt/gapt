package gapt.formats.json

import gapt.proofs.lk.LKProof
import gapt.formats.json.lk.LKProofCodec._
import org.specs2.mutable.Specification
import io.circe.parser._

class JsonToDocTest extends Specification {
  "The JSON to Doc converter" should {
    "convert and parse a small LK proof" in {
      val p: LKProof = gapt.examples.LinearExampleProof( 3 )
      val json = _lkProofEncoder( p )
      val rendered = JsonToDoc( json ).render( 80 )
      val parsed = parse( rendered )
      parsed must beRight( json )
    }

    "convert and parse a bigger proof" in {
      val p: LKProof = gapt.examples.theories.nat.add0l.combined()
      val json = _lkProofEncoder( p )
      val rendered = JsonToDoc( json ).render( 80 )
      val parsed = parse( rendered )
      parsed must beRight( json )
    }
  }
}
