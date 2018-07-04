package gapt.formats

import gapt.expr._
import gapt.proofs.{ DagProof, HOLSequent, SequentIndex }
import io.circe.{ Decoder, Encoder }
import gapt.formats.json.lk.LKProofCodec._
import gapt.proofs.lk.LKProof
import gapt.formats.json.ExprCodec._
import gapt.formats.json.SequentCodec._

package object json {

  implicit val varEncoder: Encoder[Var] = _varEncoder
  implicit val varDecoder: Decoder[Var] = _varDecoder

  implicit val absEncoder: Encoder[Abs] = _absEncoder
  implicit val absDecoder: Decoder[Abs] = _absDecoder

  implicit val constEncoder: Encoder[Const] = _constEncoder
  implicit val constDecoder: Decoder[Const] = _constDecoder

  implicit val exprEncoder: Encoder[Expr] = _exprEncoder
  implicit val exprDecoder: Decoder[Expr] = _exprDecoder

  implicit val formulaEncoder: Encoder[Formula] = _formulaEncoder
  implicit val formulaDecoder: Decoder[Formula] = _formulaDecoder

  implicit val holSequentEncoder: Encoder[HOLSequent] = _holSequentEncoder
  implicit val holSequentDecoder: Decoder[HOLSequent] = _holSequentDecoder

  implicit val sequentIndexEncoder: Encoder[SequentIndex] = _sequentIndexEncoder
  implicit val sequentIndexDecoder: Decoder[SequentIndex] = _sequentIndexDecoder

  implicit val lkProofEncoder: Encoder[LKProof] = _lkProofEncoder
  implicit val lkProofDecoder: Decoder[LKProof] = _lkProofDecoder

  private[json] def proofEncoder[P <: DagProof[P]]( proofCollectionEncoder: Encoder[ProofCollection[P]] ): Encoder[P] = proofCollectionEncoder.contramap( ProofCollection( _ ) )

  private[json] def proofDecoder[P <: DagProof[P]]( proofCollectionDecoder: Decoder[ProofCollection[P]] ): Decoder[P] = proofCollectionDecoder.emap { c =>
    if ( c.proofMap.isEmpty ) {
      Left( "No proof found in decoded collection" )
    } else {
      Right( c.proofMap.maxBy( _._2 )._1 )
    }
  }

}
