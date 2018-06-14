package gapt.formats.json

import org.specs2.mutable._
import gapt.expr._
import io.circe.Json
import io.circe.syntax._

class FormulaCodecTest extends Specification {
  import FormulaCodec._
  "The formula serializer" should {
    "serialize A" in {
      hof"A".asJson must_== Json.fromString( "A:o" )
    }

    "serialize P → Q" in {
      hof"P → Q".asJson must_== Json.fromString( "P → Q" )
    }

    "serialize ∀x P(x)" in {
      hof"∀x P(x)".asJson must_== Json.fromString( "∀x P(x)" )
    }
  }

  "The formula deserializer" should {
    "deserialize A" in {
      Json.fromString( "A:o" ).as[Formula] must beRight( hof"A" )
    }

    "deserialize P → Q" in {
      Json.fromString( "P → Q" ).as[Formula] must beRight( hof"P → Q" )
    }

    "deserialize ∀x P(x)" in {
      Json.fromString( "∀x P(x)" ).as[Formula] must beRight( hof"∀x P(x)" )
    }

    "fail to deserialize nonsense" in {
      Json.fromString( "O)))" ).as[Formula] must beLeft
    }

    "fail to deserialize a non-formula" in {
      Json.fromString( "x:i" ).as[Formula] must beLeft
    }
  }
}
