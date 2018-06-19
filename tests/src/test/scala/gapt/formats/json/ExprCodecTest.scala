package gapt.formats.json

import org.specs2.mutable._
import gapt.expr._
import io.circe.Json
import io.circe.syntax._

class ExprCodecTest extends Specification {

  import ExprCodec._

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

  "The expression serializer" should {
    "serialize A" in {
      le"A:o".asJson must_== Json.fromString( "A:o" )
    }

    "serialize P → Q" in {
      le"P → Q".asJson must_== Json.fromString( "P → Q" )
    }

    "serialize ∀x P(x)" in {
      le"∀x P(x)".asJson must_== Json.fromString( "∀x P(x)" )
    }

    "serialize a non-formula expression" in {
      le"f(x:i):i".asJson must_== Json.fromString( "f(x)" )
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

  "The expression deserializer" should {
    "deserialize A" in {
      Json.fromString( "A:o" ).as[Expr] must beRight( le"A:o" )
    }

    "deserialize P → Q" in {
      Json.fromString( "P → Q" ).as[Expr] must beRight( le"P → Q" )
    }

    "deserialize ∀x P(x)" in {
      Json.fromString( "∀x P(x)" ).as[Expr] must beRight( le"∀x P(x)" )
    }

    "fail to deserialize nonsense" in {
      Json.fromString( "O)))" ).as[Expr] must beLeft
    }

    "deserialize a non-formula expression" in {
      Json.fromString( "f(x:i):i" ).as[Expr] must beRight( le"f(x)" )
    }
  }

  "The variable/constant/abs deserializers" should {
    "function correctly" in {
      val List( v, c, a ) = List( hov"v", hoc"c", le"λx.x" ).map( _.asJson )

      v.as[Var] must beRight
      v.as[Const] must beLeft
      v.as[Abs] must beLeft

      c.as[Var] must beLeft
      c.as[Const] must beRight
      c.as[Abs] must beLeft

      a.as[Var] must beLeft
      a.as[Const] must beLeft
      a.as[Abs] must beRight
    }
  }
}