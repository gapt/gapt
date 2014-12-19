/*
 * TreesTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils.ds

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import trees._
import graphs._
import TreeImplicitConverters._

@RunWith(classOf[JUnitRunner])
class TreesTest extends SpecificationWithJUnit {
  "Tree" should {
    "pattern match as graphs and recursively" in {
      val lt = BinaryTree("y", LeafTree("a"), LeafTree("b"))
      ((lt) match {
          case EmptyGraph() => false
          case UnionGraph(x1, x2) => false
          case VertexGraph("y", _) => false
          case UnaryTree(_,_) => false
          case EdgeGraph(_, "y", UnionGraph(EdgeGraph(_, _, _),_)) => true
          case _ => false
      }) must beEqualTo (true)
    }
    "not be created if diamoned shaped (an acyclic graph but not a tree)" in {
      "1" in {
        val t1 = UnaryTree("3", UnaryTree("2", "1"))
        val t2 = UnaryTree("4", "0")
        val t3 = BinaryTree("5", t1,t2)
        (BinaryTree("-1", t3,t1)) must throwA[IllegalArgumentException]
      }
// commented out since the test should fail with our current semantics
// on trees: vertices (i.e. labels) may be equal even though the nodes
// themselves are different.
//
//      "2" in {
//        val t1 = UnaryTree("3", UnaryTree("2", "1"))
//        val t2 = UnaryTree("4", "0")
//        val t3 = BinaryTree("5", t1,t2)
//        val t4 = LeafTree("1")
//        (BinaryTree("-1", t3,t4)) must throwA[IllegalArgumentException]
//      }
      "3 (pointers equality)" in {
        val t1 = UnaryTree(new AnyRef{}, UnaryTree(new AnyRef{}, new AnyRef{}))
        val t2 = UnaryTree(new AnyRef{}, new AnyRef{})
        val t3 = BinaryTree(new AnyRef{}, t1,t2)
        (BinaryTree(new AnyRef{}, t3,t1)) must throwA[IllegalArgumentException]  
      }
    }

    "be created if not diamoned shaped (pointers equality)" in {
      val t1 = UnaryTree(new AnyRef{}, UnaryTree(new AnyRef{}, new AnyRef{}))
      val t2 = UnaryTree(new AnyRef{}, new AnyRef{})
      val t3 = BinaryTree(new AnyRef{}, t1,t2)
      val t4 = LeafTree(new AnyRef{})
      (BinaryTree(new AnyRef{}, t3,t4)) must not (throwA[IllegalArgumentException])
    }
    /*"be backed up by a correctly-constructed graph" in {
      val t1 = UnaryTree("d",UnaryTree("c",UnaryTree("b","a")))
      val t2 = UnaryTree("3", UnaryTree("2", "1"))
      val g10 = EdgeGraph("c", "d", VertexGraph[String]("d", EdgeGraph("b", "c", VertexGraph[String]("c", EdgeGraph("a", "b", VertexGraph[String]("b", VertexGraph[String]("a", EmptyGraph[String])))))))
      (t1.graph.vertexSet()) must beEqualTo (g10.graph.vertexSet())
      (t1.graph.edgeSet().toString) must beEqualTo (g10.graph.edgeSet().toString) // equals on DefaultEdge is comparing pointers and not values
    }*/
    /*"test creation with ArbitraryTree" in {
      val t1 = UnaryTree("d",UnaryTree("c",UnaryTree("b","a")))
      val t2 = UnaryTree("3", UnaryTree("2", "1"))
      val lt = LeafTree("y")
      (ArbitraryTree("x", t1, t2, lt)) must beLike {case ArbitraryTree("x", t1::t2::lt::Nil) => true}
      (ArbitraryTree("x", t1, t2)) must beLike {case BinaryTree("x", t1, t2) => true}
      (ArbitraryTree("x", t1)) must beLike {case UnaryTree("x", t1) => true}
      (ArbitraryTree("x")) must beLike {case LeafTree("x") => true}
    }  */
  }
}
