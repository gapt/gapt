package gapt.formats.json.et
import gapt.expr.{ Atom, Expr, Polarity }
import io.circe.{ Decoder, Encoder }
import io.circe.syntax._
import io.circe.generic.extras.semiauto._
import gapt.formats.json._
import gapt.proofs.expansion._
import gapt.formats.json.ExprCodec._
import gapt.proofs.Sequent
import io.circe.generic.extras.Configuration

import scala.util.Try

object ExpansionTreeCodec {
  implicit val conf: Configuration = Configuration.default.withDiscriminator( "name" )

  private[json] val _expansionTreeTermEncoder: Encoder[ETt] = deriveEncoder
  private[json] val _expansionTreeTermDecoder: Decoder[ETt] = deriveDecoder

  private[json] val _expansionTreeEncoder: Encoder[ExpansionTree] = deriveEncoder
  // TODO: maybe validate terms in default ExpansionTree constructor?
  private[json] val _expansionTreeDecoder: Decoder[ExpansionTree] =
    ( deriveDecoder: Decoder[ExpansionTree] ).emapTry( et => Try { et.check(); et } )

  private[json] val _expansionSequentEncoder: Encoder[Sequent[ExpansionTree]] = deriveEncoder
  private[json] val _expansionSequentDecoder: Decoder[Sequent[ExpansionTree]] = deriveDecoder

  private[json] val _expansionProofEncoder: Encoder[ExpansionProof] = _expansionSequentEncoder.contramap( _.expansionSequent )
  private[json] val _expansionProofDecoder: Decoder[ExpansionProof] = _expansionSequentDecoder.map( ExpansionProof( _ ) )
}