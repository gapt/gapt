package gapt.formats.json

import gapt.expr.{ Abs, Atom, Const, Expr, Formula, Polarity, Var, preExpr }
import gapt.formats.babel.BabelParser
import io.circe.{ Decoder, Encoder, KeyDecoder, KeyEncoder }

/**
 * Json codecs for various kinds of expressions. An expression is encoded as its Babel string.
 */
object ExprCodec {
  private[json] val _varEncoder: Encoder[Var] = Encoder.encodeString.contramap[Var]( _.toString )
  private[json] val _varDecoder: Decoder[Var] = Decoder.decodeString.emap { s =>
    BabelParser.tryParse( s ).left.map( _.getMessage ) flatMap {
      case v: Var => Right( v )
      case e      => Left( s"Expression $e cannot be read as a variable." )
    }
  }

  private[json] val _absEncoder: Encoder[Abs] = Encoder.encodeString.contramap[Abs]( _.toString )
  private[json] val _absDecoder: Decoder[Abs] = Decoder.decodeString.emap { s =>
    BabelParser.tryParse( s ).left.map( _.getMessage ) flatMap {
      case a: Abs => Right( a )
      case e      => Left( s"Expression $e is not an abstraction." )
    }
  }

  private[json] val _constEncoder: Encoder[Const] = Encoder.encodeString.contramap[Const]( _.toString )
  private[json] val _constDecoder: Decoder[Const] = Decoder.decodeString.emap { s =>
    BabelParser.tryParse( s ).left.map( _.getMessage ) flatMap {
      case c: Const => Right( c )
      case e        => Left( s"Expression $e cannot be read as a constant." )
    }
  }

  private[json] val _exprEncoder: Encoder[Expr] = Encoder.encodeString.contramap[Expr]( _.toString )
  private[json] val _exprDecoder: Decoder[Expr] = Decoder.decodeString.emap( s => BabelParser.tryParse( s ).left.map( _.getMessage ) )

  private[json] val _exprKeyEncoder: KeyEncoder[Expr] = _.toString
  private[json] val _exprKeyDecoder: KeyDecoder[Expr] = BabelParser.tryParse( _ ).toOption

  private[json] val _formulaEncoder: Encoder[Formula] = Encoder.encodeString.contramap[Formula]( _.toString )
  private[json] val _formulaDecoder: Decoder[Formula] = Decoder.decodeString.emap( s => BabelParser.tryParse( s, preExpr.TypeAnnotation( _, preExpr.Bool ) ) match {
    case Right( f ) => Right( f.asInstanceOf[Formula] )
    case Left( e )  => Left( e.getMessage )
  } )

  private[json] val _atomEncoder: Encoder[Atom] = Encoder.encodeString.contramap[Atom]( _.toString )
  private[json] val _atomDecoder: Decoder[Atom] = Decoder.decodeString.emap { s =>
    BabelParser.tryParse( s ).left.map( _.getMessage ) flatMap {
      case a: Atom => Right( a )
      case e       => Left( s"Expression $e cannot be read as an atom." )
    }
  }

  private[json] val _polarityEncoder: Encoder[Polarity] = Encoder.encodeBoolean.contramap( _.inSuc )
  private[json] val _polarityDecoder: Decoder[Polarity] = Decoder.decodeBoolean.map( Polarity( _ ) )

}
