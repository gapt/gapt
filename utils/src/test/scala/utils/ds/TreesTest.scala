/*
 * TreesTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils.ds

import org.specs._
import org.specs.runner._

import trees._
import graphs._
import TreeImplicitConverters._

class TreesTest extends SpecificationWithJUnit {
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