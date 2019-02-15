package gapt.formats

import gapt.expr._
import gapt.expr.formula.Atom
import gapt.expr.formula.Formula
import gapt.proofs.{ DagProof, HOLSequent, SequentIndex }
import io.circe.{ Decoder, Encoder, KeyDecoder, KeyEncoder }
import gapt.formats.json.lk.LKProofCodec._
import gapt.formats.json.nd.NDProofCodec._
import gapt.formats.json.et.ExpansionTreeCodec._
import gapt.proofs.lk.LKProof
import gapt.formats.json.ExprCodec._
import gapt.formats.json.SequentCodec._
import gapt.proofs.expansion.{ ETt, ExpansionProof, ExpansionSequent, ExpansionTree }
import gapt.proofs.nd.NDProof

package object json {

  implicit val varEncoder: Encoder[Var] = _varEncoder
  implicit val varDecoder: Decoder[Var] = _varDecoder

  implicit val absEncoder: Encoder[Abs] = _absEncoder
  implicit val absDecoder: Decoder[Abs] = _absDecoder

  implicit val constEncoder: Encoder[Const] = _constEncoder
  implicit val constDecoder: Decoder[Const] = _constDecoder

  implicit val exprEncoder: Encoder[Expr] = _exprEncoder
  implicit val exprDecoder: Decoder[Expr] = _exprDecoder

  implicit val exprKeyEncoder: KeyEncoder[Expr] = _exprKeyEncoder
  implicit val exprKeyDecoder: KeyDecoder[Expr] = _exprKeyDecoder

  implicit val formulaEncoder: Encoder[Formula] = _formulaEncoder
  implicit val formulaDecoder: Decoder[Formula] = _formulaDecoder

  implicit val atomEncoder: Encoder[Atom] = _atomEncoder
  implicit val atomDecoder: Decoder[Atom] = _atomDecoder

  implicit val holSequentEncoder: Encoder[HOLSequent] = _holSequentEncoder
  implicit val holSequentDecoder: Decoder[HOLSequent] = _holSequentDecoder

  implicit val sequentIndexEncoder: Encoder[SequentIndex] = _sequentIndexEncoder
  implicit val sequentIndexDecoder: Decoder[SequentIndex] = _sequentIndexDecoder

  implicit val polarityEncoder: Encoder[Polarity] = _polarityEncoder
  implicit val polarityDecoder: Decoder[Polarity] = _polarityDecoder

  implicit val lkProofEncoder: Encoder[LKProof] = _lkProofEncoder
  implicit val lkProofDecoder: Decoder[LKProof] = _lkProofDecoder

  implicit val ndProofEncoder: Encoder[NDProof] = _ndProofEncoder
  implicit val ndProofDecoder: Decoder[NDProof] = _ndProofDecoder

  implicit val expansionTreeTermEncoder: Encoder[ETt] = _expansionTreeTermEncoder
  implicit val expansionTreeTermDecoder: Decoder[ETt] = _expansionTreeTermDecoder

  implicit val expansionTreeEncoder: Encoder[ExpansionTree] = _expansionTreeEncoder
  implicit val expansionTreeDecoder: Decoder[ExpansionTree] = _expansionTreeDecoder

  implicit val expansionSequentEncoder: Encoder[ExpansionSequent] = _expansionSequentEncoder
  implicit val expansionSequentDecoder: Decoder[ExpansionSequent] = _expansionSequentDecoder

  implicit val expansionProofEncoder: Encoder[ExpansionProof] = _expansionProofEncoder
  implicit val expansionProofDecoder: Decoder[ExpansionProof] = _expansionProofDecoder

  private[json] def proofEncoder[P <: DagProof[P]]( proofCollectionEncoder: Encoder[ProofCollection[P]] ): Encoder[P] = proofCollectionEncoder.contramap( ProofCollection( _ ) )

  private[json] def proofDecoder[P <: DagProof[P]]( proofCollectionDecoder: Decoder[ProofCollection[P]] ): Decoder[P] = proofCollectionDecoder.emap { c =>
    if ( c.proofMap.isEmpty ) {
      Left( "No proof found in decoded collection" )
    } else {
      Right( c.proofMap.maxBy( _._2 )._1 )
    }
  }

}
