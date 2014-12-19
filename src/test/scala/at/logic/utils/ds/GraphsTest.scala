/*
 * GraphsTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils.ds

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import graphs._
import GraphImplicitConverters._

@RunWith(classOf[JUnitRunner])
class GraphsTest extends SpecificationWithJUnit {
  "Graph" should {
    val g1: EmptyGraph[String] = ()
    val g2: VertexGraph[String] = ("a", g1)
    val g21: VertexGraph[String] = ("b", g2)
    val g3: EdgeGraph[String] = ("a", "b", g21)
    val g4: EdgeGraph[String] = ("a", "c", EdgeGraph("b", "c", VertexGraph("c", g3)))
    val g5 = EdgeGraph("e", "f", VertexGraph("f", VertexGraph("e", EmptyGraph[String])))
    val g6: UnionGraph[String] = UnionGraph(g4, g5)
    "check extractors" in {
      (g2 match {
        case EmptyGraph() => false
        case UnionGraph(x1, x2) => false
        case VertexGraph("a", x2) => true
        case _ => false
      }) must beEqualTo (true)
    }

    /*"maintain subgraph property with vertices" in {
      (g3.graph.vertexSet().size()) must beEqualTo (2)
      (g2.graph.vertexSet().size()) must beEqualTo (1)
      (g2.graph.vertexSet().iterator.next()) must beEqualTo("a")
      (g1.graph.vertexSet().isEmpty()) must beEqualTo (true)
    }
    "maintain subgraph property with union" in {
      (g6.graph.vertexSet().size()) must beEqualTo (5)
      (g6.graph.edgeSet().size()) must beEqualTo (4)
      (g5.graph.vertexSet().size()) must beEqualTo (2)
      (g5.graph.edgeSet().size()) must beEqualTo (1)
      (g4.graph.vertexSet().size()) must beEqualTo (3)
      (g4.graph.edgeSet().size()) must beEqualTo (3)
    }
    "maintain subgraph property with edges" in {
      (g3.graph.edgeSet().size()) must beEqualTo (1)
      (g2.graph.edgeSet().isEmpty()) must beEqualTo (true)
      (g1.graph.edgeSet().isEmpty()) must beEqualTo (true)
    }
    "inductively extend" in {
      (g4.graph.vertexSet.size()) must beEqualTo (3)
      (g4.graph.edgeSet.size()) must beEqualTo (3)
    }*/
    "work correctly on vertices which have the same content but different equality method" in {
      class TestA(a: String)
      val gn1 = EmptyGraph[TestA]()
      val gn2 = VertexGraph(new TestA("t1"), gn1)
      val gn3 = VertexGraph(new TestA("t1"), gn2)
      true
    }
  }
}