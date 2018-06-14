package gapt.formats.json

import gapt.expr.{ Formula, preExpr }
import gapt.formats.babel.BabelParser
import io.circe.{ Decoder, Encoder }

object FormulaCodec {
  implicit val formulaEncoder: Encoder[Formula] = Encoder.encodeString.contramap[Formula]( _.toString )
  implicit val formulaDecoder: Decoder[Formula] = Decoder.decodeString.emap( s => BabelParser.tryParse( s, preExpr.TypeAnnotation( _, preExpr.Bool ) ) match {
    case Right( f ) => Right( f.asInstanceOf[Formula] )
    case Left( e )  => Left( e.getMessage )
  } )
}
