package gapt.formats.json.et
import gapt.expr.Expr
import io.circe.{Decoder, Encoder}
import gapt.formats.json._
import gapt.proofs.expansion._
import gapt.formats.json.ExprCodec._
import gapt.proofs.Sequent
import io.circe.derivation._

import scala.util.Try

object ExpansionTreeCodec {
  implicit val conf: Configuration = Configuration.default.withDiscriminator("name")

  private[json] val _expansionTreeTermEncoder: Encoder[ETt] = ConfiguredEncoder.derived
  private[json] val _expansionTreeTermDecoder: Decoder[ETt] = ConfiguredDecoder.derived

  private[json] val _expansionTreeEncoder: Encoder[ExpansionTree] = ConfiguredEncoder.derived
  // TODO: maybe validate terms in default ExpansionTree constructor?
  private[json] val _expansionTreeDecoder: Decoder[ExpansionTree] =
    (ConfiguredDecoder.derived: Decoder[ExpansionTree]).emapTry(et => Try { et.check(); et })

  private[json] val _expansionSequentEncoder: Encoder[Sequent[ExpansionTree]] = ConfiguredEncoder.derived
  private[json] val _expansionSequentDecoder: Decoder[Sequent[ExpansionTree]] = ConfiguredDecoder.derived

  private[json] val _expansionProofEncoder: Encoder[ExpansionProof] = _expansionSequentEncoder.contramap(_.expansionSequent)
  private[json] val _expansionProofDecoder: Decoder[ExpansionProof] = _expansionSequentDecoder.map(ExpansionProof(_))
}
