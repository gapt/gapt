/*
 * Graphs.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils

object Graphs {

    import scala.collection.jcl.Conversions._

    sealed abstract class Graph[V](var graph: org.jgrapht.DirectedGraph[V,org.jgrapht.graph.DefaultEdge])
    case class EmptyGraph[V]() extends Graph[V](new org.jgrapht.graph.ListenableDirectedGraph[V,org.jgrapht.graph.DefaultEdge](classOf[org.jgrapht.graph.DefaultEdge]))
    case class VertexGraph[V](v: V, g: Graph[V]) extends Graph[V](g.graph) {
        val vset = new java.util.HashSet[V](g.graph.vertexSet());
        graph.addVertex(v)
        g.graph = new org.jgrapht.graph.DirectedSubgraph[V,org.jgrapht.graph.DefaultEdge](graph, vset, g.graph.edgeSet())
    }
    case class EdgeGraph[V](v1: V, v2: V, g: Graph[V]) extends Graph[V](g.graph) {
        val eset = new java.util.HashSet[org.jgrapht.graph.DefaultEdge](g.graph.edgeSet());
        graph.addEdge(v1, v2)
        g.graph = new org.jgrapht.graph.DirectedSubgraph[V,org.jgrapht.graph.DefaultEdge](graph, g.graph.vertexSet(), eset)
    }
    case class UnionGraph[V](g1: Graph[V], g2: Graph[V]) extends Graph[V](g1.graph) {
        val vset1 = new java.util.HashSet[V](g1.graph.vertexSet())
        val vset2 = new java.util.HashSet[V](g2.graph.vertexSet())
        val eset1 = new java.util.HashSet[org.jgrapht.graph.DefaultEdge](g1.graph.edgeSet())
        val eset2 = new java.util.HashSet[org.jgrapht.graph.DefaultEdge](g2.graph.edgeSet())
        for (v0 <- g2.graph.vertexSet()) graph.addVertex(v0)
        for (e0 <- g2.graph.edgeSet()) graph.addEdge(graph.getEdgeSource(e0), graph.getEdgeTarget(e0), e0)
        g1.graph = new org.jgrapht.graph.DirectedSubgraph[V,org.jgrapht.graph.DefaultEdge](graph, vset1, eset1)
        g2.graph = new org.jgrapht.graph.DirectedSubgraph[V,org.jgrapht.graph.DefaultEdge](graph, vset2, eset2)
    }

    /**
     * Trees are constructed over the inductive graph type and are characterised by vertices not repeating in the subtrees.
     * 
     */
    sealed trait Tree[V] extends Graph[V] {
        def vertex: V
    }
    case class LeafTree[V](val vertex: V) extends VertexGraph[V](vertex, EmptyGraph[V]) with Tree[V]
    case class UnaryTree[V](val vertex: V, t: Tree[V]) extends EdgeGraph[V](t.vertex, vertex, VertexGraph[V](vertex, t)) with Tree[V] {
        require (!t.graph.vertexSet.contains(vertex))
    }
    case class BinaryTree[V](val vertex: V, t1: Tree[V], t2: Tree[V]) extends EdgeGraph[V](t2.vertex, vertex, EdgeGraph[V](t1.vertex, vertex, VertexGraph[V](vertex, UnionGraph(t1, t2)))) with Tree[V] {
        require (!t1.graph.vertexSet.contains(vertex) && ! t2.graph.vertexSet.contains(vertex)
        && !new java.util.HashSet[V](t1.graph.vertexSet).retainAll(t2.graph.vertexSet) /* returns true if the first set changed, i.e. contained an element fro the second set*/)
    }

    object TreeImplicitConverters {
        implicit def toLeafTree[V](v:V): LeafTree[V] = LeafTree[V](v)
        //implicit def toUnaryTree[V](v:V, t: Tree[V]): UnaryTree[V] = UnaryTree[V](v, t)
        //implicit def toBinaryTree[V](v:V, t1: Tree[V], t2: Tree[V]): BinaryTree[V] = BinaryTree[V](v, t1, t2)
    }
}
