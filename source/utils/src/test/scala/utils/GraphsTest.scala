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
import GraphImplicitConverters._
import TreeImplicitConverters._

class GraphsTest extends Specification with JUnit {
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
  "Tree" should {
    "contains no cycles" in {
        val t1 = UnaryTree("d",UnaryTree("c",UnaryTree("b","a")))
        val t2 = UnaryTree("3", UnaryTree("2", "1"))
        (new org.jgrapht.alg.CycleDetector[String, org.jgrapht.graph.DefaultEdge](t1.graph).detectCycles()) must beEqual (false)
        (BinaryTree("X", t1, t2)) mustNot throwA [java.lang.IllegalArgumentException]
        (UnaryTree("a", "a")) must throwA [java.lang.IllegalArgumentException]
    }
    "pattern match as graphs and recursively" in {
        val lt = ArbitraryTree("y", LeafTree("a"), LeafTree("b"), LeafTree("c"))
        ((lt) match {
            case EmptyGraph() => false
            case UnionGraph(x1, x2) => false
            case VertexGraph("y", _) => false
            case UnaryTree(_,_) => false
            case EdgeGraph(_, "y", UnionGraph(EdgeGraph(_, _, _),_)) => true
            case _ => false
        }) must beEqual (true)
    }
    "be backed up by a correctly-constructed graph" in {
        val t1 = UnaryTree("d",UnaryTree("c",UnaryTree("b","a")))
        val t2 = UnaryTree("3", UnaryTree("2", "1"))
        val g10 = EdgeGraph("c", "d", VertexGraph[String]("d", EdgeGraph("b", "c", VertexGraph[String]("c", EdgeGraph("a", "b", VertexGraph[String]("b", VertexGraph[String]("a", EmptyGraph[String])))))))
        (t1.graph.vertexSet()) must beEqual (g10.graph.vertexSet())
        (t1.graph.edgeSet().toString) must beEqual (g10.graph.edgeSet().toString) // equals on DefaultEdge is comparing pointers and not values
    }
    "test creation with ArbitraryTree" in {
        val t1 = UnaryTree("d",UnaryTree("c",UnaryTree("b","a")))
        val t2 = UnaryTree("3", UnaryTree("2", "1"))
        val lt = LeafTree("y")
        (ArbitraryTree("x", t1, t2, lt)) must beLike {case ArbitraryTree("x", t1::t2::lt::Nil) => true}
        (ArbitraryTree("x", t1, t2)) must beLike {case BinaryTree("x", t1, t2) => true}
        (ArbitraryTree("x", t1)) must beLike {case UnaryTree("x", t1) => true}
        (ArbitraryTree("x")) must beLike {case LeafTree("x") => true}
    }
  }
}