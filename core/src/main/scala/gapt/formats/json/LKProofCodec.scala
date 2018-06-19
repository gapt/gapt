package gapt.formats.json
import gapt.proofs.lk._
import io.circe.{ Decoder, Encoder, HCursor, Json }
import io.circe.syntax._
import io.circe.generic.auto._
import ExprCodec._
import SequentCodec._

object LKProofCodec {
  implicit val lkCollectionEncoder: Encoder[ProofCollection[LKProof]] = new ProofCollectionEncoder[LKProof]( encodeLK )

  implicit val lkCollectionDecoder: Decoder[ProofCollection[LKProof]] = new ProofCollectionDecoder[LKProof]( decodeLK )

  /**
   * Given a map from LKProofs to integers, serializes a single proof by
   * looking up its subproofs in the collection and replacing them with their numbers.
   */
  private def encodeLK( proofMap: Map[LKProof, Int] ): Encoder[LKProof] = {
    implicit val lkNumEncoder: Encoder[LKProof] = p => Json.fromInt( proofMap( p ) )

    proof => {
      val obj = proof match {
        case p @ ProofLink( _, _ )                  => p.asJson
        case TopAxiom                               => TopAxiom.asJson
        case BottomAxiom                            => BottomAxiom.asJson
        case p @ LogicalAxiom( _ )                  => p.asJson
        case p @ ReflexivityAxiom( _ )              => p.asJson
        case p @ WeakeningLeftRule( _, _ )          => p.asJson
        case p @ WeakeningRightRule( _, _ )         => p.asJson
        case p @ ContractionLeftRule( _, _, _ )     => p.asJson
        case p @ ContractionRightRule( _, _, _ )    => p.asJson
        case p @ CutRule( _, _, _, _ )              => p.asJson
        case p @ NegLeftRule( _, _ )                => p.asJson
        case p @ NegRightRule( _, _ )               => p.asJson
        case p @ AndLeftRule( _, _, _ )             => p.asJson
        case p @ AndRightRule( _, _, _, _ )         => p.asJson
        case p @ OrLeftRule( _, _, _, _ )           => p.asJson
        case p @ OrRightRule( _, _, _ )             => p.asJson
        case p @ ImpLeftRule( _, _, _, _ )          => p.asJson
        case p @ ImpRightRule( _, _, _ )            => p.asJson
        case p @ ForallLeftRule( _, _, _, _, _ )    => p.asJson
        case p @ ForallRightRule( _, _, _, _ )      => p.asJson
        case p @ ExistsLeftRule( _, _, _, _ )       => p.asJson
        case p @ ExistsRightRule( _, _, _, _, _ )   => p.asJson
        case p @ ExistsSkLeftRule( _, _, _, _, _ )  => p.asJson
        case p @ ForallSkRightRule( _, _, _, _, _ ) => p.asJson
        case p @ EqualityLeftRule( _, _, _, _ )     => p.asJson
        case p @ EqualityRightRule( _, _, _, _ )    => p.asJson
        case p @ InductionRule( _, _, _ )           => p.asJson
        case p @ DefinitionLeftRule( _, _, _ )      => p.asJson
        case p @ DefinitionRightRule( _, _, _ )     => p.asJson
      }

      obj.mapObject( ( "name", Json.fromString( s"${proof.longName}" ) ) +: _ )
    }
  }

  /**
   * Given a map from integers to proofs,
   * @param m
   * @return
   */
  private def decodeLK( m: Map[Int, LKProof] ): Decoder[LKProof] = {
    implicit val lkNumDecoder: Decoder[LKProof] = Decoder.decodeInt.emap( i => m.get( i ).toRight( s"Subproof $i not found" ) )

    c: HCursor => {
      val d = c.downField( "name" )
      d.as[String].flatMap { name =>
        val e = d.delete
        name match {
          case "ProofLink"            => e.as[ProofLink].map( _.asInstanceOf[LKProof] )
          case "TopAxiom"             => e.as[TopAxiom.type].map( _.asInstanceOf[LKProof] )
          case "BottomAxiom"          => e.as[BottomAxiom.type].map( _.asInstanceOf[LKProof] )
          case "LogicalAxiom"         => e.as[LogicalAxiom].map( _.asInstanceOf[LKProof] )
          case "ReflexivityAxiom"     => e.as[ReflexivityAxiom].map( _.asInstanceOf[LKProof] )
          case "WeakeningLeftRule"    => e.as[WeakeningLeftRule].map( _.asInstanceOf[LKProof] )
          case "WeakeningRightRule"   => e.as[WeakeningRightRule].map( _.asInstanceOf[LKProof] )
          case "ContractionLeftRule"  => e.as[ContractionLeftRule].map( _.asInstanceOf[LKProof] )
          case "ContractionRightRule" => e.as[ContractionRightRule].map( _.asInstanceOf[LKProof] )
          case "CutRule"              => e.as[CutRule].map( _.asInstanceOf[LKProof] )
          case "NegLeftRule"          => e.as[NegLeftRule].map( _.asInstanceOf[LKProof] )
          case "NegRightRule"         => e.as[NegRightRule].map( _.asInstanceOf[LKProof] )
          case "AndLeftRule"          => e.as[AndLeftRule].map( _.asInstanceOf[LKProof] )
          case "AndRightRule"         => e.as[AndRightRule].map( _.asInstanceOf[LKProof] )
          case "OrLeftRule"           => e.as[OrLeftRule].map( _.asInstanceOf[LKProof] )
          case "OrRightRule"          => e.as[OrRightRule].map( _.asInstanceOf[LKProof] )
          case "ImpLeftRule"          => e.as[ImpLeftRule].map( _.asInstanceOf[LKProof] )
          case "ImpRightRule"         => e.as[ImpRightRule].map( _.asInstanceOf[LKProof] )
          case "ForallLeftRule"       => e.as[ForallLeftRule].map( _.asInstanceOf[LKProof] )
          case "ForallRightRule"      => e.as[ForallRightRule].map( _.asInstanceOf[LKProof] )
          case "ExistsLeftRule"       => e.as[ExistsLeftRule].map( _.asInstanceOf[LKProof] )
          case "ExistsRightRule"      => e.as[ExistsRightRule].map( _.asInstanceOf[LKProof] )
          case "ExistsSkLeftRule"     => e.as[ExistsSkLeftRule].map( _.asInstanceOf[LKProof] )
          case "ForallSkRightRule"    => e.as[ForallSkRightRule].map( _.asInstanceOf[LKProof] )
          case "EqualityLeftRule"     => e.as[EqualityLeftRule].map( _.asInstanceOf[LKProof] )
          case "EqualityRightRule"    => e.as[EqualityRightRule].map( _.asInstanceOf[LKProof] )
          case "InductionRule"        => e.as[InductionRule].map( _.asInstanceOf[LKProof] )
          case "DefinitionLeftRule"   => e.as[DefinitionLeftRule].map( _.asInstanceOf[LKProof] )
          case "DefinitionRightRule"  => e.as[DefinitionRightRule].map( _.asInstanceOf[LKProof] )
        }
      }

    }
  }
}
