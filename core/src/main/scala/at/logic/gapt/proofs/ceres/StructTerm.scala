package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr.{ To, MonomorphicLogicalC, SymbolA, LambdaExpression }
import at.logic.gapt.utils.ds.trees.{ BinaryTree, UnaryTree, LeafTree, Tree }

/**
 * Created by marty on 10/19/15.
 */
// since case classes may be DAGs, we give a method to convert to a tree
// (for, e.g. displaying purposes)

package structterm {
  case object TimesSymbol extends SymbolA {
    def unique = "TimesSymbol"
    override def toString = "⊗"
    def toCode = "TimesSymbol"
  }

  case object PlusSymbol extends SymbolA {
    def unique = "PlusSymbol"
    override def toString = "⊕"
    def toCode = "PlusSymbol"
  }

  case object DualSymbol extends SymbolA {
    def unique = "DualSymbol"
    override def toString = "∼"
    def toCode = "DualSymbol"
  }

  case object EmptyTimesSymbol extends SymbolA {
    def unique = "EmptyTimesSymbol"
    override def toString = "ε_⊗"
    def toCode = "EmptyTimesSymbol"
  }

  case object EmptyPlusSymbol extends SymbolA {
    def unique = "EmptyPlusSymbol"
    override def toString = "ε_⊕"
    def toCode = "EmptyPlusSymbol"
  }

  object TimesC extends MonomorphicLogicalC( TimesSymbol.toString, To -> ( To -> To ) )
  object PlusC extends MonomorphicLogicalC( PlusSymbol.toString, To -> ( To -> To ) )
  object DualC extends MonomorphicLogicalC( DualSymbol.toString, To -> To )
  object EmptyTimesC extends MonomorphicLogicalC( EmptyTimesSymbol.toString, To )
  object EmptyPlusC extends MonomorphicLogicalC( EmptyPlusSymbol.toString, To )

}

import structterm._

object structToExpressionTree {
  def apply[Data]( s: Struct[Data] ): Tree[LambdaExpression] = s match {
    case A( f, _ )               => LeafTree( f )
    case Dual( sub )             => UnaryTree( DualC(), apply( sub ) )
    case Times( left, right, _ ) => BinaryTree( TimesC(), apply( left ), apply( right ) )
    case Plus( left, right )     => BinaryTree( PlusC(), apply( left ), apply( right ) )
    case EmptyTimesJunction()    => LeafTree( EmptyTimesC() )
    case EmptyPlusJunction()     => LeafTree( EmptyPlusC() )
  }

  // constructs struct Tree without empty leaves.
  def prunedTree[Data]( s: Struct[Data] ): Tree[LambdaExpression] = s match {
    case A( f, _ )   => LeafTree( f )
    case Dual( sub ) => UnaryTree( DualC(), prunedTree( sub ) )
    case Times( left, right, _ ) =>
      val l = prunedTree( left )
      val r = prunedTree( right )
      if ( l.isInstanceOf[LeafTree[LambdaExpression]] && ( l.vertex == EmptyTimesC || l.vertex == EmptyPlusC ) )
        if ( r.isInstanceOf[LeafTree[LambdaExpression]] && ( r.vertex == EmptyTimesC || r.vertex == EmptyPlusC ) ) LeafTree( EmptyTimesC() )
        else r
      else if ( r.isInstanceOf[LeafTree[LambdaExpression]] && ( r.vertex == EmptyTimesC || r.vertex == EmptyPlusC ) ) l
      else BinaryTree( TimesC(), l, r )
    case Plus( left, right ) =>
      val l = prunedTree( left )
      val r = prunedTree( right )
      if ( l.isInstanceOf[LeafTree[LambdaExpression]] && ( l.vertex == EmptyTimesC || l.vertex == EmptyPlusC ) )
        if ( r.isInstanceOf[LeafTree[LambdaExpression]] && ( r.vertex == EmptyTimesC || r.vertex == EmptyPlusC ) ) LeafTree( EmptyPlusC() )
        else r
      else if ( r.isInstanceOf[LeafTree[LambdaExpression]] && ( r.vertex == EmptyTimesC || r.vertex == EmptyPlusC ) ) l
      else BinaryTree( PlusC(), l, r )
    case EmptyTimesJunction() => LeafTree( EmptyTimesC() )
    case EmptyPlusJunction()  => LeafTree( EmptyPlusC() )
  }

}

