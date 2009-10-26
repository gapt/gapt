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
      val g2 = VertexGraph[String]("a", Nil, g1)
      val g3 = VertexGraph[String]("b", "a"::Nil, g2)
      val g4 = VertexGraph[String]("c", "a"::"b"::Nil, g3)
    "maintain subgraph property with vertices" in {
        (g3.graph.vertexSet().size()) must beEqual (2)
        (g2.graph.vertexSet().size()) must beEqual (1)
        (g2.graph.vertexSet().iterator.next()) must beEqual("a")
        (g1.graph.vertexSet().isEmpty()) must beEqual (true)
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
  "Tree" should {
      val t1 = LeafTree[String]("a")
      val t2 = LinearTree[String]("b", t1)
      val t3 = LinearTree[String]("c", t2)
      val t4 = LinearTree[String]("d", t3)
    "contains no cycles" in {
        (new org.jgrapht.alg.CycleDetector[String, org.jgrapht.graph.DefaultEdge](t4.graph).detectCycles()) must beEqual (false)
    }
  }
}