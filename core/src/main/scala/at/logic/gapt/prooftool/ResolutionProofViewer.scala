package at.logic.gapt.prooftool

import at.logic.gapt.proofs.proofs.Proof

class ResolutionProofViewer[T]( name: String, proof: Proof[T] ) extends ProofToolViewer[Proof[T]]( name, proof ) {
  override type MainComponentType = DrawResolutionProof[T]
  override def createMainComponent( fSize: Int ) = new DrawResolutionProof[T]( this, proof, fSize, None, "" )
}
