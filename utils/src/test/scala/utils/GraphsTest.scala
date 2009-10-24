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
    "not contain a vertex when empty" in {
        (Graph[String]).containsVertex("x") must beEqual (false)
    }
    "contain a vertex when having it" in {
        val g = Graph[String]; g.addVertex("x"); g.containsVertex("x") must beEqual (true)
    }
  }
}