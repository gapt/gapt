/*
 * Trees.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */


package at.logic.utils.ds
import at.logic.utils.logging.Logger

import acyclicGraphs._
import graphs._
import scala.collection.JavaConversions._
import scala.collection.immutable.{Set,HashSet}

package trees {
  /**
   * Trees are constructed over the inductive graph type and are characterised by vertices not repeating in the leaves.
   *
   */

  trait Tree[V] extends AGraph[V] {
    require {isTree} // important, read remark above
    private[trees] def isTree: Boolean // TODO optimize isTree (in binaryTree)
    val vertex: V
    def name: String // used to contain more information about the tree, like rule names in LK
    def fold[T](leafF: V => T)(unaryF: (T, V) => T)(binaryF: (T,T,V)=> T): T

    def leaves: Set[LeafTree[V]]
  }

  class LeafTree[V](override val vertex: V) extends LeafAGraph[V](vertex) with Tree[V] {
    private[trees] def isTree: Boolean = true // any leaf is a tree
    def fold[T](leafF: V => T)(unaryF: (T, V) => T)(binaryF: (T,T,V)=> T): T = leafF(vertex)
    def leaves = new HashSet() + this
  }
  object LeafTree {
    def apply[V](vertex: V) = new LeafTree[V](vertex)
    def unapply[V](t: Tree[V]) = t match {
      case t: LeafTree[_] => Some(t.vertex)
      case t: Tree[_] => None
    }
  }

  class UnaryTree[V](override val vertex: V, override val t: Tree[V]) extends UnaryAGraph[V](vertex, t) with Tree[V] {
    private[trees] def isTree: Boolean = true // any unary tree is a tree if its child component is a tree, therefore, as we accept a valid tree as argument, nothing should be done here.
    def fold[T](leafF: V => T)(unaryF: (T, V) => T)(binaryF: (T,T,V)=> T): T = unaryF(t.fold(leafF)(unaryF)(binaryF), vertex)
    def leaves = t.leaves
  }
  object UnaryTree {
    def apply[V](vertex: V, t: Tree[V]) = new UnaryTree[V](vertex, t)
    def unapply[V](t: Tree[V]) = t match {
      case t: UnaryTree[_] => Some((t.vertex, t.t))
      case t: Tree[_] => None
    }
  }
  class BinaryTree[V](override val vertex: V, override val t1: Tree[V], override val t2: Tree[V]) extends BinaryAGraph[V](vertex,t1,t2) with Tree[V] {

    // we must check that no subtree in one sub component is equal to a subtree in the other component
    // it is enough to check leaves only
    private[trees] def isTree: Boolean =
      (t1.leaves & t2.leaves).isEmpty

    def fold[T](leafF: V => T)(unaryF: (T, V) => T)(binaryF: (T,T,V)=> T): T = binaryF(t1.fold(leafF)(unaryF)(binaryF), t2.fold(leafF)(unaryF)(binaryF), vertex)
    def leaves = t1.leaves ++ t2.leaves
  }
  object BinaryTree {
    def apply[V](vertex: V, t1: Tree[V], t2: Tree[V]) = new BinaryTree[V](vertex, t1, t2)
    def unapply[V](t: Tree[V]) = t match {
      case t: BinaryTree[_] => Some((t.vertex, t.t1, t.t2))
      case t: Tree[_] => None
    }
  }

  /*class ArbitraryTree[+V] private (override val vertex: V, override val lastParent: Tree[V], override val restParents: List[Tree[V]], graph: Graph[V]) extends ArbitraryAGraph[V](vertex,lastParent,restParents,graph) with Tree[V]
  // TODO add a require so it remains a tree (check no vertex repeats and new vertex is new)
  object ArbitraryTree extends Logger {
    def apply[V](vertex: V, parents: Tree[V]*) = {val ls = parents.toList; ls match {
      case Nil => LeafTree[V](vertex)
      case t::Nil => UnaryTree[V](vertex, t)
      case t1::t2::Nil => BinaryTree[V](vertex, t1, t2)
      case t::tls => applyRec[V](vertex, tls, ls, EdgeGraph[V](t.vertex, vertex, VertexGraph[V](vertex, t)))
    }}
    def applyRec[V](vertex: V, trees: List[Tree[V]], allParents: List[Tree[V]], graph: Graph[V]): ArbitraryTree[V] = trees match {
      case Nil => error("The recursive call in arbitrary tree is always called on at least two arguments as the other cases are being handled by unary and binary trees", new AssertionError())
      case t::Nil => new ArbitraryTree[V](vertex, allParents.head, allParents.tail, graph)
      case t::tls => applyRec[V](vertex, tls, allParents, EdgeGraph[V](t.vertex, vertex, UnionGraph[V](graph, t)))
    }
    def unapply[V](t: Tree[V]) = t match {
      case t: ArbitraryTree[_] => Some((t.vertex, (t.lastParent::t.restParents)))
      case t: Tree[_] => None
    }
  }  */

  object TreeImplicitConverters {
    implicit def toLeafTree[V](v:V): LeafTree[V] = LeafTree[V](v)
    implicit def toUnaryTree[V](pair: Tuple2[V, Tree[V]]): UnaryTree[V] = UnaryTree[V](pair._1, pair._2)
    implicit def toBinaryTree[V](triple: Tuple3[V, Tree[V], Tree[V]]): BinaryTree[V] = BinaryTree[V](triple._1, triple._2, triple._3)
  }
}
