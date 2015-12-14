package at.logic.gapt.prooftool

import at.logic.gapt.utils.ds.trees.Tree

/**
 * Created by sebastian on 12/13/15.
 */
class TreeViewer[T]( name: String, tree: Tree[T] ) extends ProofToolViewer[Tree[T]]( name, tree ) {
  override type MainComponentType = DrawTree
  override def createMainComponent( fSize: Int ) = new DrawTree( this, tree, fSize, "" )
}
