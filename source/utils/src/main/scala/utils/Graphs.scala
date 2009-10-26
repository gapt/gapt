/*
 * Graphs.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils

object Graphs {

    sealed abstract class Graph[V](var graph: org.jgrapht.DirectedGraph[V,org.jgrapht.graph.DefaultEdge])
    case class EmptyGraph[V]() extends Graph[V](new org.jgrapht.graph.ListenableDirectedGraph[V,org.jgrapht.graph.DefaultEdge](classOf[org.jgrapht.graph.DefaultEdge]))
    case class VertexGraph[V](v: V, vls: List[V], g: Graph[V]) extends Graph[V](g.graph) {
        graph.addVertex(v)
        for (v0 <- vls) graph.addEdge(v0, v)
        g.graph = {val vset = new java.util.HashSet[V](graph.vertexSet()); vset.remove(v); val eset = graph.edgeSet(); new org.jgrapht.graph.DirectedSubgraph[V,org.jgrapht.graph.DefaultEdge](graph, vset, eset)}
    }

    sealed trait Tree[V] extends Graph[V] {
        def vertex: V
    }
    case class LeafTree[V](vertex: V) extends VertexGraph[V](vertex, Nil, EmptyGraph[V]) with Tree[V]
    case class LinearTree[V](vertex: V, t: Tree[V]) extends VertexGraph[V](vertex, t.vertex::Nil, t) with Tree[V]
}
