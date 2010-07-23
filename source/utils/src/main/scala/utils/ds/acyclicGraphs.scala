/*
 * acyclicGraphs.scala
 *
 * Inductive definition of acyclic graphs, this is essentially AGraphs where the parents can contain the same elements
 */

package at.logic.utils.ds

import at.logic.utils.ds.graphs._
import at.logic.utils.logging.Logger

package acyclicGraphs {
  trait AGraph[+V] extends Graph[V] {
    val vertex: V
    def name: String // used to contain more information about the AGraph, like rule names in LK
  }

  class LeafAGraph[+V](val vertex: V) extends VertexGraph[V](vertex, EmptyGraph[V]) with AGraph[V] {
    override def equals(a: Any) = a match {
      case LeafAGraph(v) => vertex == v
      case _ => false
    }
    override def hashCode = vertex.hashCode
    override def toString = vertex.toString
    def name = "Leaf"
  }
  object LeafAGraph {
    def apply[V](vertex: V) = new LeafAGraph[V](vertex)
    def unapply[V](t: AGraph[V]) = t match {
      case t: LeafAGraph[_] => Some(t.vertex)
      case t: AGraph[_] => None
    }
  }
  class UnaryAGraph[+V](val vertex: V, val t: AGraph[V]) extends EdgeGraph[V](t.vertex, vertex, VertexGraph[V](vertex, t)) with AGraph[V] {
    override def equals(a: Any) = a match {
      case UnaryAGraph(v,up) => vertex == v && t == up
      case _ => false
    }
    override def hashCode = vertex.hashCode + t.hashCode
    override def toString = vertex.toString + " (" + t.toString + ")"
    def name = "Unary"
    def latexQAGraph = "[{." + vertex.toString + "} ({" + name + ")}"
  }
  object UnaryAGraph {
    def apply[V](vertex: V, t: AGraph[V]) = new UnaryAGraph[V](vertex, t)
    def unapply[V](t: AGraph[V]) = t match {
      case t: UnaryAGraph[_] => Some((t.vertex, t.t))
      case t: AGraph[_] => None
    }
  }
  class BinaryAGraph[+V](val vertex: V, val t1: AGraph[V], val t2: AGraph[V]) extends EdgeGraph[V](t2.vertex, vertex, UnionGraph[V](EdgeGraph[V](t1.vertex, vertex, VertexGraph[V](vertex, t1)), t2)) with AGraph[V] {
    override def equals(a: Any) = a match {
      case BinaryAGraph(v,up1,up2) => vertex == v && t1 == up1 && t2 == up2
      case _ => false
    }
    override def hashCode = vertex.hashCode + t1.hashCode + t2.hashCode
    override def toString = vertex.toString + " (" + t1.toString + ", " + t2.toString + ")"
    def name = "Binary"
  }
  object BinaryAGraph {
    def apply[V](vertex: V, t1: AGraph[V], t2: AGraph[V]) = new BinaryAGraph[V](vertex, t1, t2)
    def unapply[V](t: AGraph[V]) = t match {
      case t: BinaryAGraph[_] => Some((t.vertex, t.t1, t.t2))
      case t: AGraph[_] => None
    }
  }
  class ArbitraryAGraph[+V] protected (val vertex: V, val lastParent: AGraph[V], val restParents: List[AGraph[V]], graph: Graph[V]) extends EdgeGraph[V](lastParent.vertex, vertex, UnionGraph[V](graph, lastParent)) with AGraph[V] {
    override def equals(a: Any) = a match {
      case ArbitraryAGraph(v,ls) => vertex == v && ls == lastParent::restParents
      case _ => false
    }
    override def hashCode = vertex.hashCode + (lastParent::restParents).hashCode
    override def toString = vertex.toString + " (" + (lastParent::restParents) + ")"
    def name = "Arbitrary"
  }

  object ArbitraryAGraph extends Logger {
    def apply[V](vertex: V, parents: AGraph[V]*) = {val ls = parents.toList; ls match {
      case Nil => LeafAGraph[V](vertex)
      case t::Nil => UnaryAGraph[V](vertex, t)
      case t1::t2::Nil => BinaryAGraph[V](vertex, t1, t2)
      case t::tls => applyRec[V](vertex, tls, ls, EdgeGraph[V](t.vertex, vertex, VertexGraph[V](vertex, t)))
    }}
    def applyRec[V](vertex: V, AGraphs: List[AGraph[V]], allParents: List[AGraph[V]], graph: Graph[V]): ArbitraryAGraph[V] = AGraphs match {
      case Nil => error("The recursive call in arbitrary AGraph is always called on at least two arguments as the other cases are being handled by unary and binary AGraphs", new AssertionError())
      case t::Nil => new ArbitraryAGraph[V](vertex, allParents.head, allParents.tail, graph)
      case t::tls => applyRec[V](vertex, tls, allParents, EdgeGraph[V](t.vertex, vertex, UnionGraph[V](graph, t)))
    }
    def unapply[V](t: AGraph[V]) = t match {
      case t: ArbitraryAGraph[_] => Some((t.vertex, (t.lastParent::t.restParents)))
      case t: AGraph[_] => None
    }
  }
}
