/*
 * GraphsTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils

import org.specs._
import org.specs.runner._

import Graphs._

class GraphsTest extends Specification with JUnit {
  "Graph" should {
      val g1 = EmptyGraph[String]
      val g2 = VertexGraph("a", g1)
      val g3 = EdgeGraph("a", "b", VertexGraph("b", g2))
      val g4 = EdgeGraph("a", "c", EdgeGraph("b", "c", VertexGraph("c", g3)))
      val g5 = EdgeGraph("e", "f", VertexGraph("f", VertexGraph("e", EmptyGraph[String])))
      val g6 = UnionGraph(g4, g5)
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
  import TreeImplicitConverters._
  "Tree" should {
        val t1 = UnaryTree("d",UnaryTree("c",UnaryTree("b","a")))
        val t2 = UnaryTree("3", UnaryTree("2", "1"))
    "contains no cycles" in {
        (new org.jgrapht.alg.CycleDetector[String, org.jgrapht.graph.DefaultEdge](t1.graph).detectCycles()) must beEqual (false)
        (BinaryTree("X", t1, t2)) must throwA [java.lang.IllegalArgumentException]
        (UnaryTree("a", "a")) must throwA [java.lang.IllegalArgumentException]
    }
    "be backed up by a correctly-constructed graph" in {
        val g10 = EdgeGraph("c", "d", VertexGraph[String]("d", EdgeGraph("b", "c", VertexGraph[String]("c", EdgeGraph("a", "b", VertexGraph[String]("b", VertexGraph[String]("a", EmptyGraph[String])))))))
        (t1.graph.vertexSet()) must beEqual (g10.graph.vertexSet())
        (t1.graph.edgeSet().toString) must beEqual (g10.graph.edgeSet().toString) // equals on DefaultEdge is comparing pointers and not values
    }

  }
}