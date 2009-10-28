/*
 * Graphs.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils
import logging.Logger

object Graphs {

    import scala.collection.jcl.Conversions._

    trait Graph[V] {
        var graph: org.jgrapht.DirectedGraph[V,org.jgrapht.graph.DefaultEdge] = null
    }
    class EmptyGraph[V] extends Graph[V] { graph = new org.jgrapht.graph.ListenableDirectedGraph[V,org.jgrapht.graph.DefaultEdge](classOf[org.jgrapht.graph.DefaultEdge])}
    object EmptyGraph {
        def apply[V]() = new EmptyGraph[V]
        def unapply[V](g: Graph[_]) = g match {
            case g: EmptyGraph[_] => true
            case g: Graph[_] => false
        }
    }
    class VertexGraph[V](val v: V, val g: Graph[V]) extends Graph[V] {
        graph = g.graph
        val vset = new java.util.HashSet[V](g.graph.vertexSet())
        graph.addVertex(v)
        g.graph = new org.jgrapht.graph.DirectedSubgraph[V,org.jgrapht.graph.DefaultEdge](graph, vset, g.graph.edgeSet())
    }
    object VertexGraph {
        def apply[V](v: V, g: Graph[V]) = new VertexGraph[V](v,g)
        def unapply[V](g: Graph[V]) = g match {
            case g: VertexGraph[_] => Some((g.v, g.g))
            case g: Graph[_] => None
        }
    }
    class EdgeGraph[V](val v1: V, val v2: V, val g: Graph[V]) extends Graph[V] {
        graph = g.graph
        val eset = new java.util.HashSet[org.jgrapht.graph.DefaultEdge](g.graph.edgeSet());
        graph.addEdge(v1, v2)
        g.graph = new org.jgrapht.graph.DirectedSubgraph[V,org.jgrapht.graph.DefaultEdge](graph, g.graph.vertexSet(), eset)
    }
    object EdgeGraph {
        def apply[V](v1: V, v2: V, g: Graph[V]) = new EdgeGraph[V](v1,v2,g)
        def unapply[V](g: Graph[V]) = g match {
            case g: EdgeGraph[_] => Some((g.v1, g.v2, g.g))
            case g: Graph[_] => None
        }
    }
    class UnionGraph[V](val g1: Graph[V], val g2: Graph[V]) extends Graph[V] {
        graph = g1.graph
        val vset1 = new java.util.HashSet[V](g1.graph.vertexSet())
        val vset2 = new java.util.HashSet[V](g2.graph.vertexSet())
        val eset1 = new java.util.HashSet[org.jgrapht.graph.DefaultEdge](g1.graph.edgeSet())
        val eset2 = new java.util.HashSet[org.jgrapht.graph.DefaultEdge](g2.graph.edgeSet())
        for (v0 <- g2.graph.vertexSet()) graph.addVertex(v0)
        for (e0 <- g2.graph.edgeSet()) graph.addEdge(graph.getEdgeSource(e0), graph.getEdgeTarget(e0), e0)
        g1.graph = new org.jgrapht.graph.DirectedSubgraph[V,org.jgrapht.graph.DefaultEdge](graph, vset1, eset1)
        g2.graph = new org.jgrapht.graph.DirectedSubgraph[V,org.jgrapht.graph.DefaultEdge](graph, vset2, eset2)
    }
    object UnionGraph {
        def apply[V](g1: Graph[V], g2: Graph[V]) = new UnionGraph[V](g1, g2)
        def unapply[V](g: Graph[V]) = g match {
            case g: UnionGraph[_] => Some((g.g1, g.g2))
            case g: Graph[_] => None
        }
    }
    /**
     * Trees are constructed over the inductive graph type and are characterised by vertices not repeating in the subtrees.
     * 
     */

    trait Tree[V] extends Graph[V] {
        val vertex: V
    }

    class LeafTree[V](val vertex: V) extends VertexGraph[V](vertex, EmptyGraph[V]) with Tree[V]
    object LeafTree {
        def apply[V](vertex: V) = new LeafTree[V](vertex)
        def unapply[V](t: Tree[V]) = t match {
            case t: LeafTree[_] => Some(t.vertex)
            case t: Tree[_] => None
        }
    }
    class UnaryTree[V](val vertex: V, val t: Tree[V]) extends EdgeGraph[V](t.vertex, vertex, VertexGraph[V](vertex, t)) with Tree[V] {
        require (!t.graph.vertexSet.contains(vertex))
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

    case object TreeImplicitConverters {
        implicit def toLeafTree[V](v:V): LeafTree[V] = LeafTree[V](v)
        //implicit def toUnaryTree[V](v:V, t: Tree[V]): UnaryTree[V] = UnaryTree[V](v, t)
        //implicit def toBinaryTree[V](v:V, t1: Tree[V], t2: Tree[V]): BinaryTree[V] = BinaryTree[V](v, t1, t2)
    }
}
