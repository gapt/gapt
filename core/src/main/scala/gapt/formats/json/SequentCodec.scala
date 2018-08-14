package gapt.formats.json

import gapt.proofs.{ Ant, HOLSequent, SequentIndex, Suc }
import io.circe._
import io.circe.generic.semiauto._

object SequentCodec {
  private[json] val _holSequentEncoder: Encoder[HOLSequent] = deriveEncoder[HOLSequent]
  private[json] val _holSequentDecoder: Decoder[HOLSequent] = deriveDecoder[HOLSequent]

  private[json] val _sequentIndexEncoder: Encoder[SequentIndex] = Encoder.encodeInt.contramap( _.toInt )
  private[json] val _sequentIndexDecoder: Decoder[SequentIndex] = Decoder.decodeInt.map( SequentIndex.fromSignedInt )
}

