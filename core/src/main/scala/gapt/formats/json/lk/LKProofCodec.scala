package gapt.formats.json.lk

import gapt.formats.json.{ lkProofEncoder => _, lkProofDecoder => _, _ }
import gapt.proofs.lk._
import io.circe.Decoder.Result
import io.circe._
import io.circe.generic.auto._
import io.circe.syntax._

object LKProofCodec {
  private[json] val lkCollectionEncoder: Encoder[ProofCollection[LKProof]] = ProofCollectionCodec.proofCollectionEncoder[LKProof]( encodeLK )

  private[json] val lkCollectionDecoder: Decoder[ProofCollection[LKProof]] = ProofCollectionCodec.proofCollectionDecoder[LKProof]( decodeLK )

  private[json] val _lkProofEncoder = proofEncoder[LKProof]( lkCollectionEncoder )

  private[json] val _lkProofDecoder = proofDecoder[LKProof]( lkCollectionDecoder )

  /**
   * Given an encoder for subproofs, this encodes a single LK proof.
   */
  private def encodeLK( subEncoder: Encoder[LKProof] ): Encoder[LKProof] = {
    implicit val e: Encoder[LKProof] = subEncoder

    {
      case p @ ProofLink( _, _ )                => p.asJson
      case TopAxiom                             => TopAxiom.asJson
      case BottomAxiom                          => BottomAxiom.asJson
      case p @ LogicalAxiom( _ )                => p.asJson
      case p @ ReflexivityAxiom( _ )            => p.asJson
      case p @ WeakeningLeftRule( _, _ )        => p.asJson
      case p @ WeakeningRightRule( _, _ )       => p.asJson
      case p @ ContractionLeftRule( _, _, _ )   => p.asJson
      case p @ ContractionRightRule( _, _, _ )  => p.asJson
      case p @ CutRule( _, _, _, _ )            => p.asJson
      case p @ NegLeftRule( _, _ )              => p.asJson
      case p @ NegRightRule( _, _ )             => p.asJson
      case p @ AndLeftRule( _, _, _ )           => p.asJson
      case p @ AndRightRule( _, _, _, _ )       => p.asJson
      case p @ OrLeftRule( _, _, _, _ )         => p.asJson
      case p @ OrRightRule( _, _, _ )           => p.asJson
      case p @ ImpLeftRule( _, _, _, _ )        => p.asJson
      case p @ ImpRightRule( _, _, _ )          => p.asJson
      case p @ ForallLeftRule( _, _, _, _, _ )  => p.asJson
      case p @ ForallRightRule( _, _, _, _ )    => p.asJson
      case p @ ExistsLeftRule( _, _, _, _ )     => p.asJson
      case p @ ExistsRightRule( _, _, _, _, _ ) => p.asJson
      case p @ ExistsSkLeftRule( _, _, _, _ )   => p.asJson
      case p @ ForallSkRightRule( _, _, _, _ )  => p.asJson
      case p @ EqualityLeftRule( _, _, _, _ )   => p.asJson
      case p @ EqualityRightRule( _, _, _, _ )  => p.asJson
      case p @ InductionRule( _, _, _ )         => p.asJson
      case p @ DefinitionLeftRule( _, _, _ )    => p.asJson
      case p @ DefinitionRightRule( _, _, _ )   => p.asJson
    }
  }

  /**
   * Given a rule name, a cursor, and a decoder for subproofs, this decodes a single LK proof.
   */
  private def decodeLK( name: String, c: ACursor, subDecoder: Decoder[LKProof] ): Result[LKProof] = {
    implicit val d: Decoder[LKProof] = subDecoder
    name match {
      case "ProofLink"            => c.as[ProofLink]
      case "TopAxiom"             => c.as[TopAxiom.type]
      case "BottomAxiom"          => c.as[BottomAxiom.type]
      case "LogicalAxiom"         => c.as[LogicalAxiom]
      case "ReflexivityAxiom"     => c.as[ReflexivityAxiom]
      case "WeakeningLeftRule"    => c.as[WeakeningLeftRule]
      case "WeakeningRightRule"   => c.as[WeakeningRightRule]
      case "ContractionLeftRule"  => c.as[ContractionLeftRule]
      case "ContractionRightRule" => c.as[ContractionRightRule]
      case "CutRule"              => c.as[CutRule]
      case "NegLeftRule"          => c.as[NegLeftRule]
      case "NegRightRule"         => c.as[NegRightRule]
      case "AndLeftRule"          => c.as[AndLeftRule]
      case "AndRightRule"         => c.as[AndRightRule]
      case "OrLeftRule"           => c.as[OrLeftRule]
      case "OrRightRule"          => c.as[OrRightRule]
      case "ImpLeftRule"          => c.as[ImpLeftRule]
      case "ImpRightRule"         => c.as[ImpRightRule]
      case "ForallLeftRule"       => c.as[ForallLeftRule]
      case "ForallRightRule"      => c.as[ForallRightRule]
      case "ExistsLeftRule"       => c.as[ExistsLeftRule]
      case "ExistsRightRule"      => c.as[ExistsRightRule]
      case "ExistsSkLeftRule"     => c.as[ExistsSkLeftRule]
      case "ForallSkRightRule"    => c.as[ForallSkRightRule]
      case "EqualityLeftRule"     => c.as[EqualityLeftRule]
      case "EqualityRightRule"    => c.as[EqualityRightRule]
      case "InductionRule"        => c.as[InductionRule]
      case "DefinitionLeftRule"   => c.as[DefinitionLeftRule]
      case "DefinitionRightRule"  => c.as[DefinitionRightRule]
      case _                      => Left( DecodingFailure( s"Rule $name not recognized.", Nil ) )
    }
  }
}
