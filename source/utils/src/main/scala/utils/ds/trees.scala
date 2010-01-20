/*
 * Trees.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils.ds
import at.logic.utils.logging.Logger

import graphs._
import scala.collection.jcl.Conversions._

package trees {
  /**
   * Trees are constructed over the inductive graph type and are characterised by vertices not repeating in the subtrees.
   *
   */

  trait Tree[V] extends Graph[V] {
    val vertex: V
  }

  class LeafTree[V](val vertex: V) extends VertexGraph[V](vertex, EmptyGraph[V]) with Tree[V] {
    override def equals(a: Any) = a match {
      case tree: LeafTree[_] => vertex == tree.vertex
    }
    override def hashCode = vertex.hashCode
  }
  object LeafTree {
    def apply[V](vertex: V) = new LeafTree[V](vertex)
    def unapply[V](t: Tree[V]) = t match {
      case t: LeafTree[_] => Some(t.vertex)
      case t: Tree[_] => None
    }
  }
  class UnaryTree[V](val vertex: V, val t: Tree[V]) extends EdgeGraph[V](t.vertex, vertex, VertexGraph[V](vertex, t)) with Tree[V] {
    require (!t.graph.vertexSet.contains(vertex))
    override def equals(a: Any) = a match {
      case tree: UnaryTree[_] => vertex == tree.vertex && t == tree.t
    }
    override def hashCode = vertex.hashCode + t.hashCode
  }
  object UnaryTree {
    def apply[V](vertex: V, t: Tree[V]) = new UnaryTree[V](vertex, t)
    def unapply[V](t: Tree[V]) = t match {
      case t: UnaryTree[_] => Some((t.vertex, t.t))
      case t: Tree[_] => None
    }
  }
  class BinaryTree[V](val vertex: V, val t1: Tree[V], val t2: Tree[V]) extends EdgeGraph[V](t2.vertex, vertex, UnionGraph[V](EdgeGraph[V](t1.vertex, vertex, VertexGraph[V](vertex, t1)), t2)) with Tree[V] {
    require (!t1.graph.vertexSet.contains(vertex) && ! t2.graph.vertexSet.contains(vertex)
    && !new java.util.HashSet[V](t1.graph.vertexSet).removeAll(t2.graph.vertexSet) /* returns true if the first set changed, i.e. contained an element from the second set*/)
    override def equals(a: Any) = a match {
      case tree: BinaryTree[_] => vertex == tree.vertex && t1 == tree.t1 && t2 == tree.t2
    }
    override def hashCode = vertex.hashCode + t1.hashCode + t2.hashCode
  }
  object BinaryTree {
    def apply[V](vertex: V, t1: Tree[V], t2: Tree[V]) = new BinaryTree[V](vertex, t1, t2)
    def unapply[V](t: Tree[V]) = t match {
      case t: BinaryTree[_] => Some((t.vertex, t.t1, t.t2))
      case t: Tree[_] => None
    }
  }
  class ArbitraryTree[V] private (val vertex: V, val lastParent: Tree[V], val restParents: List[Tree[V]], graph: Graph[V]) extends EdgeGraph[V](lastParent.vertex, vertex, UnionGraph[V](graph, lastParent)) with Tree[V]
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
      case t::Nil => new ArbitraryTree[V](vertex, allParents.first, allParents.tail, graph)
      case t::tls => applyRec[V](vertex, tls, allParents, EdgeGraph[V](t.vertex, vertex, UnionGraph[V](graph, t)))
    }
    def unapply[V](t: Tree[V]) = t match {
      case t: ArbitraryTree[_] => Some((t.vertex, (t.lastParent::t.restParents)))
      case t: Tree[_] => None
    }
  }

  object TreeImplicitConverters {
    implicit def toLeafTree[V](v:V): LeafTree[V] = LeafTree[V](v)
    implicit def toUnaryTree[V](pair: Tuple2[V, Tree[V]]): UnaryTree[V] = UnaryTree[V](pair._1, pair._2)
    implicit def toBinaryTree[V](triple: Tuple3[V, Tree[V], Tree[V]]): BinaryTree[V] = BinaryTree[V](triple._1, triple._2, triple._3)
  }
}
