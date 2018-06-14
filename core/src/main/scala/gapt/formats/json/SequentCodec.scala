package gapt.formats.json

import gapt.proofs.HOLSequent
import io.circe._, io.circe.generic.semiauto._
import FormulaCodec._

object SequentCodec {
  implicit val sequentEncoder: Encoder[HOLSequent] = deriveEncoder[HOLSequent]
  implicit val sequentDecoder: Decoder[HOLSequent] = deriveDecoder[HOLSequent]
}

