package gapt.formats.json

import org.specs2.mutable._
import gapt.expr._
import io.circe.Json

class ExprCodecTest extends Specification {

  import ExprCodec._

  "The formula serializer" should {
    "serialize A" in {
      _formulaEncoder(hof"A") must_== Json.fromString("A:o")
    }

    "serialize P → Q" in {
      _formulaEncoder(hof"P → Q") must_== Json.fromString("P → Q")
    }

    "serialize ∀x P(x)" in {
      _formulaEncoder(hof"∀x P(x)") must_== Json.fromString("∀x P(x)")
    }
  }

  "The expression serializer" should {
    "serialize A" in {
      _exprEncoder(le"A:o") must_== Json.fromString("A:o")
    }

    "serialize P → Q" in {
      _exprEncoder(le"P → Q") must_== Json.fromString("P → Q")
    }

    "serialize ∀x P(x)" in {
      _exprEncoder(le"∀x P(x)") must_== Json.fromString("∀x P(x)")
    }

    "serialize a non-formula expression" in {
      _exprEncoder(le"f(x:i):i") must_== Json.fromString("f(x)")
    }
  }

  "The formula deserializer" should {
    "deserialize A" in {
      _formulaDecoder.decodeJson(Json.fromString("A:o")) must beRight(hof"A")
    }

    "deserialize P → Q" in {
      _formulaDecoder.decodeJson(Json.fromString("P → Q")) must beRight(hof"P → Q")
    }

    "deserialize ∀x P(x)" in {
      _formulaDecoder.decodeJson(Json.fromString("∀x P(x)")) must beRight(hof"∀x P(x)")
    }

    "fail to deserialize nonsense" in {
      _formulaDecoder.decodeJson(Json.fromString("O)))")) must beLeft
    }

    "fail to deserialize a non-formula" in {
      _formulaDecoder.decodeJson(Json.fromString("x:i")) must beLeft
    }
  }

  "The expression deserializer" should {
    "deserialize A" in {
      _exprDecoder.decodeJson(Json.fromString("A:o")) must beRight(le"A:o")
    }

    "deserialize P → Q" in {
      _exprDecoder.decodeJson(Json.fromString("P → Q")) must beRight(le"P → Q")
    }

    "deserialize ∀x P(x)" in {
      _exprDecoder.decodeJson(Json.fromString("∀x P(x)")) must beRight(le"∀x P(x)")
    }

    "fail to deserialize nonsense" in {
      _exprDecoder.decodeJson(Json.fromString("O)))")) must beLeft
    }

    "deserialize a non-formula expression" in {
      _exprDecoder.decodeJson(Json.fromString("f(x:i):i")) must beRight(le"f(x)")
    }
  }

  "The variable/constant/abs deserializers" should {
    "function correctly" in {
      val List(v, c, a) = List(hov"v", hoc"c", le"λx.x").map(_exprEncoder(_))

      _varDecoder.decodeJson(v) must beRight
      _constDecoder.decodeJson(v) must beLeft
      _absDecoder.decodeJson(v) must beLeft

      _varDecoder.decodeJson(c) must beLeft
      _constDecoder.decodeJson(c) must beRight
      _absDecoder.decodeJson(c) must beLeft

      _varDecoder.decodeJson(a) must beLeft
      _constDecoder.decodeJson(a) must beLeft
      _absDecoder.decodeJson(a) must beRight
    }
  }
}
