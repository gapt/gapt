/*
 * acyclicGraphs.scala
 *
 * Inductive definition of acyclic graphs, this is essentially trees where the parents can contain the same elements. It is based on graph and like
 * the graph it is a connected acyclic graph
 */

package at.logic.utils.ds

import at.logic.utils.ds.graphs._
import scala.collection.immutable.{HashSet, HashMap}

// it should be called conntected acyclic graphs as it always generates connected components
// important note! The current equality between trees always refer to pointers equality and ignore the vertex. Two notes about it:
// 1) the pointer equality does not need to be implemented recursively up the agraph as we deal with immutable objects and the equality of of the roots imply the equality of all sub-agraphs. So always only
// roots should be compared and the object equals behave as expected (no need to override it)
// 2) in case a different behavior is expected, the different agraphs should be extended and the equals method be override, but again, as we deal with immutable objects, only the roots should be compared.
package acyclicGraphs {

trait AGraph[+V] extends Graph[V] {

    val vertex: V
    def name: String // used to contain more information about the AGraph, like rule names in LK
    def contains[T >: AGraph[V]](sub: T): Boolean

  /* collects all subnodes visiting each node only once */
  def nodes[_ >: V] () : HashSet[AGraph[_]] = nodes(HashSet[AGraph[_]]())
  def nodes[_ >: V](visited : HashSet[AGraph[_]]) : HashSet[AGraph[_]] =
    if (visited contains this)
      visited
    else this match {
      case LeafAGraph(v) => visited + this
      case UnaryAGraph(v, child) =>
        child.nodes(visited) + this
    case BinaryAGraph(v, child1, child2) =>
      val nvisited1 = child1.nodes(visited)
      val nvisited2 = child2.nodes(nvisited1)
      nvisited2 + this
    case ArbitraryAGraph(v, children) =>
      children.foldLeft(visited)((vs, child) => child.nodes(vs)) + this
    }

  /* number of different nodes in the proof */
  def unique_size = nodes.size

  /* number of nodes in proof */
  def size[_ >: V] () : Int = size(HashMap[AGraph[_], Int]())(this)
  def size[_ >: V](visited : Map[AGraph[_], Int]) : Map[AGraph[_],Int] =
    if (visited contains this)
      visited
    else this match {
      case LeafAGraph(v) => visited + ((this, 1))
      case UnaryAGraph(v, child) =>
        val nvisited = child.size(visited)
        nvisited + ((this, nvisited(child)+1))
      case BinaryAGraph(v, child1, child2) =>
        val nvisited1 = child1.size(visited)
        val nvisited2 = child2.size(nvisited1)
        nvisited2 + ((this, nvisited2(child1) + nvisited2(child2) +1))
      case ArbitraryAGraph(v, children) =>
        val nvisited = children.foldLeft(visited)((vs, child) => child.size(vs))
        val nsize = children.foldLeft(1)((s, child) => s + nvisited(child))
        nvisited + ((this,nsize))
    }


}

  class LeafAGraph[+V](val vertex: V) extends VertexGraph[V](vertex, EmptyGraph[V]) with AGraph[V] {
    override def hashCode = vertex.hashCode
    override def toString = vertex.toString
    def name = "Leaf"
    def contains[T >: AGraph[V]](sub: T) = this == sub
  }
  object LeafAGraph {
    def apply[V](vertex: V) = new LeafAGraph[V](vertex)
    def unapply[V](t: AGraph[V]) = t match {
      case t: LeafAGraph[_] => Some(t.vertex)
      case t: AGraph[_] => None
    }
  }
  class UnaryAGraph[+V](val vertex: V, val t: AGraph[V]) extends EdgeGraph[V](t.vertex, vertex, VertexGraph[V](vertex, t)) with AGraph[V] {
    override def hashCode = vertex.hashCode + t.hashCode
    override def toString = vertex.toString + " (" + t.toString + ")"
    def name = "Unary"
    def latexQAGraph = "[{." + vertex.toString + "} ({" + name + ")}"
    def contains[T >: AGraph[V]](sub: T) = (this == sub) || t.contains(sub)
  }
  object UnaryAGraph {
    def apply[V](vertex: V, t: AGraph[V]) = new UnaryAGraph[V](vertex, t)
    def unapply[V](t: AGraph[V]) = t match {
      case t: UnaryAGraph[V] => Some((t.vertex, t.t))
      case t: AGraph[V] => None
    }
  }
  class BinaryAGraph[+V](val vertex: V, val t1: AGraph[V], val t2: AGraph[V]) extends EdgeGraph[V](t2.vertex, vertex, UnionGraph[V](EdgeGraph[V](t1.vertex, vertex, VertexGraph[V](vertex, t1)), t2)) with AGraph[V] {
    override def hashCode = vertex.hashCode + t1.hashCode + t2.hashCode
    override def toString = vertex.toString + " (" + t1.toString + ", " + t2.toString + ")"
    def name = "Binary"
    def contains[T >: AGraph[V]](sub: T) = (this == sub) || t1.contains(sub) || t2.contains(sub)
  }
  object BinaryAGraph {
    def apply[V](vertex: V, t1: AGraph[V], t2: AGraph[V]) = new BinaryAGraph[V](vertex, t1, t2)
    def unapply[V](t: AGraph[V]) = t match {
      case t: BinaryAGraph[V] => Some((t.vertex, t.t1, t.t2))
      case t: AGraph[V] => None
    }
  }
  class ArbitraryAGraph[+V] protected (val vertex: V, val lastParent: AGraph[V], val restParents: List[AGraph[V]], graph: Graph[V])
    extends EdgeGraph[V](lastParent.vertex, vertex, UnionGraph[V](graph, lastParent)) with AGraph[V] {
    override def hashCode = vertex.hashCode + (lastParent::restParents).hashCode
    override def toString = vertex.toString + " (" + (lastParent::restParents) + ")"
    def name = "Arbitrary"
    def contains[T >: AGraph[V]](sub: T) = this == sub || lastParent.contains(sub) || restParents.exists(x => x.contains(sub))
  }

  object ArbitraryAGraph {
    def apply[V](vertex: V, parents: AGraph[V]*) = {val ls = parents.toList; ls match {
      case Nil => LeafAGraph[V](vertex)
      case t::Nil => UnaryAGraph[V](vertex, t)
      case t1::t2::Nil => BinaryAGraph[V](vertex, t1, t2)
      case t::tls => applyRec[V](vertex, tls, ls, EdgeGraph[V](t.vertex, vertex, VertexGraph[V](vertex, t)))
    }}
    def applyRec[V](vertex: V, AGraphs: List[AGraph[V]], allParents: List[AGraph[V]], graph: Graph[V]): ArbitraryAGraph[V] = AGraphs match {
      case Nil => throw new AssertionError("The recursive call in arbitrary AGraph is always called on at least two arguments as the other cases are being handled by unary and binary AGraphs")
      case t::Nil => new ArbitraryAGraph[V](vertex, allParents.head, allParents.tail, graph)
      case t::tls => applyRec[V](vertex, tls, allParents, EdgeGraph[V](t.vertex, vertex, UnionGraph[V](graph, t)))
    }
    def unapply[V](t: AGraph[V]) = t match {
      case t: ArbitraryAGraph[V] => Some((t.vertex, (t.lastParent::t.restParents)))
      case t: AGraph[V] => None
    }
  }
}
