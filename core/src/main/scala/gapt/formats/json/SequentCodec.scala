package gapt.formats.json

import gapt.proofs.{ Ant, HOLSequent, SequentIndex, Suc }
import io.circe._
import io.circe.generic.semiauto._
import ExprCodec._

object SequentCodec {
  implicit val sequentEncoder: Encoder[HOLSequent] = deriveEncoder[HOLSequent]
  implicit val sequentDecoder: Decoder[HOLSequent] = deriveDecoder[HOLSequent]

  implicit val sequentIndexEncoder: Encoder[SequentIndex] = Encoder.encodeInt.contramap( _.toInt )
  implicit val sequentIndexDecoder: Decoder[SequentIndex] = Decoder.decodeInt.map( SequentIndex.fromSignedInt )
}

