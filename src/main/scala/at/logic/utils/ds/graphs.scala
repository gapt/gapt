/*
 * Graphs.scala
 *
 * Inductive (and unintuitive) definition of graphs.
 * We use this definition in order to have uniformity of presentation in the system as both global (intuitive) graphs
 * and trees (which are inductive) can be based on inductive graphs. The graphs defined are connected graphs. i.e. a new graph 
 * can be defined inductively by conneting a new edge or a vertex to the existing graph.
 */

package at.logic.utils.ds

package graphs {

import scala.collection.JavaConversions._
import at.logic.utils.logging.Logger

trait Graph[+V] {
  // this value is computed when needed from the structure of the inductive graph
  //def graph: org.jgrapht.DirectedGraph[V,DefaultEdge]

  //needed for interfacing with java
  //def getGraph(): org.jgrapht.DirectedGraph[V,DefaultEdge] = graph
}
class EmptyGraph[+V] extends Graph[V] {
    //def graph: org.jgrapht.DirectedGraph[V,DefaultEdge] = new org.jgrapht.graph.DefaultDirectedGraph[V,DefaultEdge](classOf[DefaultEdge])
  }
object EmptyGraph {
    def apply[V]() = new EmptyGraph[V]
    def unapply[V](g: Graph[V]) = g match {
      case g: EmptyGraph[V] => true
      case g: Graph[V] => false
    }
  }
class VertexGraph[+V](val v: V, val g: Graph[V]) extends Graph[V] {
    /*def graph = {
      val ret = g.graph
      ret.addVertex(v)
      ret
    }*/
  }
object VertexGraph {
    def apply[V](v: V, g: Graph[V]) = new VertexGraph[V](v,g)
    def unapply[V](g: Graph[V]) = g match {
      case g: VertexGraph[V] => Some((g.v, g.g))
      case g: Graph[V] => None
    }
  }
class EdgeGraph[+V](val v1: V, val v2: V, val g: Graph[V]) extends Graph[V]{
    /*def graph = {
      val ret = g.graph
      ret.addEdge(v1,v2)
      ret
    }*/
  }
object EdgeGraph {
    def apply[V](v1: V, v2: V, g: Graph[V]) = new EdgeGraph[V](v1,v2,g)
    def unapply[V](g: Graph[V]) = g match {
      case g: EdgeGraph[V] => Some((g.v1, g.v2, g.g))
      case g: Graph[V] => None
    }
  }
class UnionGraph[+V](val g1: Graph[V], val g2: Graph[V]) extends Graph[V]{
    /*def graph = {
      val ret = g1.graph
      val g2graph = g2.graph
      for (v0 <- g2graph.vertexSet()) ret.addVertex(v0)
      for (e0 <- g2graph.edgeSet()) ret.addEdge(ret.getEdgeSource(e0), ret.getEdgeTarget(e0), e0)
      ret
    }*/
  }
object UnionGraph {
    def apply[V](g1: Graph[V], g2: Graph[V]) = new UnionGraph[V](g1, g2)
    def unapply[V](g: Graph[V]) = g match {
      case g: UnionGraph[V] => Some((g.g1, g.g2))
      case g: Graph[V] => None
    }
  }
object GraphImplicitConverters {
    implicit def toEmptyGraph[V](u: Unit): EmptyGraph[V] = EmptyGraph[V]
    implicit def toVertexGraph[V](pair: Tuple2[V, Graph[V]]): VertexGraph[V] = VertexGraph[V](pair._1, pair._2)
    implicit def toEdgeGraph[V](triple: Tuple3[V, V, Graph[V]]): EdgeGraph[V] = EdgeGraph[V](triple._1, triple._2, triple._3)
    implicit def toUnionGraph[V](triple: Tuple2[Graph[V], Graph[V]]): UnionGraph[V] = UnionGraph[V](triple._1, triple._2)
  }
}
