package gapt.formats.json

import gapt.proofs.lk.LKProof
import gapt.formats.json.lk.LKProofCodec._
import io.circe.Json
import org.specs2.mutable.Specification
import org.specs2.specification.core.Fragments
import sequence.LinearExampleProof

class JsonToDocTest extends Specification {
  private def roundtrip( d: Json ) =
    io.circe.parser.parse( JsonToDoc( d ).render( 80 ) ) must beRight( d )

  "The JSON to Doc converter" should {
    "convert and parse a small LK proof" in {
      val p: LKProof = LinearExampleProof( 3 )
      roundtrip( _lkProofEncoder( p ) )
    }

    "convert and parse a bigger proof" in {
      val p: LKProof = gapt.examples.theories.nat.add0l.combined()
      roundtrip( _lkProofEncoder( p ) )
    }
  }

  "roundtrip" in {
    "double quotes" in roundtrip( Json.fromString( "\"" ) )
    "newlines" in roundtrip( Json.fromString( "\n" ) )
    "null byte" in roundtrip( Json.fromString( "\u0000" ) )
    Fragments.foreach( 0 until 20 )( i =>
      s"control character $i" in
        roundtrip( Json.fromString( i.toChar.toString ) ) )
    "decimals" in roundtrip( Json.fromBigDecimal( BigDecimal( "12e-5" ) ) )
    "zero point one" in roundtrip( Json.fromBigDecimal( BigDecimal( "0.1" ) ) )
  }
}
