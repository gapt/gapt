package at.logic.gapt.prooftool

import at.logic.gapt.proofs.ceres.Struct

class StructViewer[D]( name: String, tree: Struct[D] ) extends ScrollableProofToolViewer[Struct[D]]( name, tree ) {
  override type MainComponentType = DrawStruct[D]
  override def createMainComponent = new DrawStruct( this, tree, "" )
}
