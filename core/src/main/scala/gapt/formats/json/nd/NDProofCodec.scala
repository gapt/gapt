package gapt.formats.json.nd

import gapt.formats.json.{ ndProofDecoder => _, ndProofEncoder => _, _ }
import gapt.proofs.nd._
import io.circe.Decoder.Result
import io.circe._
import io.circe.syntax._
import io.circe.generic.auto._

object NDProofCodec {
  private[json] val ndCollectionEncoder: Encoder[ProofCollection[NDProof]] = ProofCollectionCodec.proofCollectionEncoder[NDProof]( encodeND )

  private[json] val ndCollectionDecoder: Decoder[ProofCollection[NDProof]] = ProofCollectionCodec.proofCollectionDecoder[NDProof]( decodeND )

  private[json] val _ndProofEncoder = proofEncoder[NDProof]( ndCollectionEncoder )

  private[json] val _ndProofDecoder = proofDecoder[NDProof]( ndCollectionDecoder )

  /**
   * Given an encoder for subproofs, this encodes a single LK proof.
   */
  private def encodeND( subEncoder: Encoder[NDProof] ): Encoder[NDProof] = {
    implicit val e: Encoder[NDProof] = subEncoder

    {
      case p @ WeakeningRule( _, _ )            => p.asJson
      case p @ ContractionRule( _, _, _ )       => p.asJson
      case p @ LogicalAxiom( _ )                => p.asJson
      case p @ AndElim1Rule( _ )                => p.asJson
      case p @ AndElim2Rule( _ )                => p.asJson
      case p @ AndIntroRule( _, _ )             => p.asJson
      case p @ OrElimRule( _, _, _, _, _ )      => p.asJson
      case p @ OrIntro1Rule( _, _ )             => p.asJson
      case p @ OrIntro2Rule( _, _ )             => p.asJson
      case p @ ImpElimRule( _, _ )              => p.asJson
      case p @ ImpIntroRule( _, _ )             => p.asJson
      case p @ NegElimRule( _, _ )              => p.asJson
      case p @ NegIntroRule( _, _ )             => p.asJson
      case TopIntroRule                         => TopIntroRule.asJson
      case p @ BottomElimRule( _, _ )           => p.asJson
      case p @ ForallIntroRule( _, _, _ )       => p.asJson
      case p @ ForallElimRule( _, _ )           => p.asJson
      case p @ ExistsIntroRule( _, _, _, _ )    => p.asJson
      case p @ ExistsElimRule( _, _, _, _ )     => p.asJson
      case p @ TheoryAxiom( _ )                 => p.asJson
      case p @ EqualityElimRule( _, _, _, _ )   => p.asJson
      case p @ EqualityIntroRule( _ )           => p.asJson
      case p @ InductionRule( _, _, _ )         => p.asJson
      case p @ ExcludedMiddleRule( _, _, _, _ ) => p.asJson
      case p @ DefinitionRule( _, _ )           => p.asJson
    }
  }

  /**
   * Given a rule name, a cursor, and a decoder for subproofs, this decodes a single LK proof.
   */
  private def decodeND( name: String, c: ACursor, subDecoder: Decoder[NDProof] ): Result[NDProof] = {
    implicit val d: Decoder[NDProof] = subDecoder
    name match {
      case "WeakeningRule"      => c.as[WeakeningRule]
      case "ContractionRule"    => c.as[ContractionRule]
      case "LogicalAxiom"       => c.as[LogicalAxiom]
      case "AndElim1Rule"       => c.as[AndElim1Rule]
      case "AndElim2Rule"       => c.as[AndElim2Rule]
      case "AndIntroRule"       => c.as[AndIntroRule]
      case "OrElimRule"         => c.as[OrElimRule]
      case "OrIntro1Rule"       => c.as[OrIntro1Rule]
      case "OrIntro2Rule"       => c.as[OrIntro2Rule]
      case "ImpElimRule"        => c.as[ImpElimRule]
      case "ImpIntroRule"       => c.as[ImpIntroRule]
      case "NegElimRule"        => c.as[NegElimRule]
      case "NegIntroRule"       => c.as[NegIntroRule]
      case "TopIntroRule"       => c.as[TopIntroRule.type]
      case "BottomElimRule"     => c.as[BottomElimRule]
      case "ForallIntroRule"    => c.as[ForallIntroRule]
      case "ForallElimRule"     => c.as[ForallElimRule]
      case "ExistsIntroRule"    => c.as[ExistsIntroRule]
      case "ExistsElimRule"     => c.as[ExistsElimRule]
      case "TheoryAxiom"        => c.as[TheoryAxiom]
      case "EqualityElimRule"   => c.as[EqualityElimRule]
      case "EqualityIntroRule"  => c.as[EqualityIntroRule]
      case "InductionRule"      => c.as[InductionRule]
      case "ExcludedMiddleRule" => c.as[ExcludedMiddleRule]
      case "DefinitionRule"     => c.as[DefinitionRule]
      case _                    => Left( DecodingFailure( s"Rule $name not recognized.", Nil ) )
    }
  }
}
