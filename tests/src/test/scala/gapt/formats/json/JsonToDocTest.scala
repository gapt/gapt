package gapt.formats.json

import gapt.proofs.lk.LKProof
import gapt.formats.json.lk.LKProofCodec._
import io.circe.Json
import org.specs2.mutable.Specification
import io.circe.parser._
import org.specs2.specification.core.Fragments

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

  "roundtrip" in {
    def roundtrip( d: Json ) =
      io.circe.parser.parse( JsonToDoc( d ).render( 80 ) ) must beRight( d )

    "double quotes" in roundtrip( Json.fromString( "\"" ) )
    "newlines" in roundtrip( Json.fromString( "\n" ) )
    "null byte" in roundtrip( Json.fromString( "\0" ) )
    Fragments.foreach( 0 until 20 )( i =>
      s"control character $i" in
        roundtrip( Json.fromString( i.toChar.toString ) ) )
    "decimals" in roundtrip( Json.fromBigDecimal( BigDecimal( "12e-5" ) ) )
    "zero point one" in roundtrip( Json.fromBigDecimal( BigDecimal( "0.1" ) ) )
  }
}
