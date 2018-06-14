package gapt.formats.json

import gapt.expr.{ Expr, Formula, preExpr }
import gapt.formats.babel.BabelParser
import io.circe.{ Decoder, Encoder }

object FormulaCodec {
  implicit val exprEncoder: Encoder[Expr] = Encoder.encodeString.contramap[Expr]( _.toString )
  implicit val exprDecoder: Decoder[Expr] = Decoder.decodeString.emap( s => BabelParser.tryParse( s ).left.map( _.getMessage ) )

  implicit val formulaEncoder: Encoder[Formula] = Encoder.encodeString.contramap[Formula]( _.toString )
  implicit val formulaDecoder: Decoder[Formula] = Decoder.decodeString.emap( s => BabelParser.tryParse( s, preExpr.TypeAnnotation( _, preExpr.Bool ) ) match {
    case Right( f ) => Right( f.asInstanceOf[Formula] )
    case Left( e )  => Left( e.getMessage )
  } )
}
