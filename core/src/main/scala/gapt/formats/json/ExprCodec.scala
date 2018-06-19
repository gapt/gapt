package gapt.formats.json

import gapt.expr.{ Abs, Const, Expr, Formula, Var, preExpr }
import gapt.formats.babel.BabelParser
import io.circe.{ Decoder, Encoder }

/**
 * Json codecs for various kinds of expressions. An expression is encoded as its Babel string.
 */
object ExprCodec {
  implicit val varEncoder: Encoder[Var] = Encoder.encodeString.contramap[Var]( _.toString )
  implicit val varDecoder: Decoder[Var] = Decoder.decodeString.emap { s =>
    BabelParser.tryParse( s ).left.map( _.getMessage ) flatMap {
      case v: Var => Right( v )
      case e      => Left( s"Expression $e cannot be read as a variable." )
    }
  }

  implicit val absEncoder: Encoder[Abs] = Encoder.encodeString.contramap[Abs]( _.toString )
  implicit val absDecoder: Decoder[Abs] = Decoder.decodeString.emap { s =>
    BabelParser.tryParse( s ).left.map( _.getMessage ) flatMap {
      case a: Abs => Right( a )
      case e      => Left( s"Expression $e is not an abstraction." )
    }
  }

  implicit val constEncoder: Encoder[Const] = Encoder.encodeString.contramap[Const]( _.toString )
  implicit val constDecoder: Decoder[Const] = Decoder.decodeString.emap { s =>
    BabelParser.tryParse( s ).left.map( _.getMessage ) flatMap {
      case c: Const => Right( c )
      case e        => Left( s"Expression $e cannot be read as a constant." )
    }
  }

  implicit val exprEncoder: Encoder[Expr] = Encoder.encodeString.contramap[Expr]( _.toString )
  implicit val exprDecoder: Decoder[Expr] = Decoder.decodeString.emap( s => BabelParser.tryParse( s ).left.map( _.getMessage ) )

  implicit val formulaEncoder: Encoder[Formula] = Encoder.encodeString.contramap[Formula]( _.toString )
  implicit val formulaDecoder: Decoder[Formula] = Decoder.decodeString.emap( s => BabelParser.tryParse( s, preExpr.TypeAnnotation( _, preExpr.Bool ) ) match {
    case Right( f ) => Right( f.asInstanceOf[Formula] )
    case Left( e )  => Left( e.getMessage )
  } )
}
