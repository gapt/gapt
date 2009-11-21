/*
 * Graphs.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils.ds

package graphs {

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
  object GraphImplicitConverters {
    implicit def toEmptyGraph[V](u: Unit): EmptyGraph[V] = EmptyGraph[V]
    implicit def toVertexGraph[V](pair: Tuple2[V, Graph[V]]): VertexGraph[V] = VertexGraph[V](pair._1, pair._2)
    implicit def toEdgeGraph[V](triple: Tuple3[V, V, Graph[V]]): EdgeGraph[V] = EdgeGraph[V](triple._1, triple._2, triple._3)
    implicit def toUnionGraph[V](triple: Tuple2[Graph[V], Graph[V]]): UnionGraph[V] = UnionGraph[V](triple._1, triple._2)
  }
}
