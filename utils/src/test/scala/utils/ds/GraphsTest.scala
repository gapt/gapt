/*
 * GraphsTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils.ds

import org.specs._
import org.specs.runner._

import graphs._
import GraphImplicitConverters._

class GraphsTest extends SpecificationWithJUnit {
  "Graph" should {
      val g1: EmptyGraph[String] = ()
      val g2: VertexGraph[String] = ("a", g1)
      val g21: VertexGraph[String] = ("b", g2)
      val g3: EdgeGraph[String] = ("a", "b", g21)
      val g4: EdgeGraph[String] = ("a", "c", EdgeGraph("b", "c", VertexGraph("c", g3)))
      val g5 = EdgeGraph("e", "f", VertexGraph("f", VertexGraph("e", EmptyGraph[String])))
      val g6: UnionGraph[String] = (g4, g5)
    "check extractors" in {
        (g2 match {
            case EmptyGraph() => false
            case UnionGraph(x1, x2) => false
            case VertexGraph("a", x2) => true
            case _ => false
        }) must beEqual (true)
    }
    "maintain subgraph property with vertices" in {
        (g3.graph.vertexSet().size()) must beEqual (2)
        (g2.graph.vertexSet().size()) must beEqual (1)
        (g2.graph.vertexSet().iterator.next()) must beEqual("a")
        (g1.graph.vertexSet().isEmpty()) must beEqual (true)
    }
    "maintain subgraph property with union" in {
        (g6.graph.vertexSet().size()) must beEqual (5)
        (g6.graph.edgeSet().size()) must beEqual (4)
        (g5.graph.vertexSet().size()) must beEqual (2)
        (g5.graph.edgeSet().size()) must beEqual (1)
        (g4.graph.vertexSet().size()) must beEqual (3)
        (g4.graph.edgeSet().size()) must beEqual (3)
    }
    "maintain subgraph property with edges" in {
        (g3.graph.edgeSet().size()) must beEqual (1)
        (g2.graph.edgeSet().isEmpty()) must beEqual (true)
        (g1.graph.edgeSet().isEmpty()) must beEqual (true)
    }
    "inductively extend" in {
        (g4.graph.vertexSet.size()) must beEqual (3)
        (g4.graph.edgeSet.size()) must beEqual (3)
    }
  }
}