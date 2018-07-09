package gapt.prooftool

import gapt.proofs.ceres.Struct

class StructViewer( name: String, tree: Struct ) extends ScrollableProofToolViewer[Struct]( name, tree ) {
  override type MainComponentType = DrawStruct
  override def createMainComponent = new DrawStruct( this, tree, "" )
}
