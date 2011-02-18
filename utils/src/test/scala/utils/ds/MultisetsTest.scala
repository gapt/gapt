/*
 * MultisetTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.utils.ds

import org.specs._
import org.specs.runner._

import Multisets._
import scala.collection.immutable.HashSet


class MultisetsTest extends SpecificationWithJUnit {
   "Multisets" should {
     val m1 = ((HashMultiset[Int] + 1) + 1) + 2

     val c0 = HashMultiset[Int]
     val c11 = HashMultiset[Int] + 1
     val c12 = HashMultiset[Int] + 2
     val c21 = (HashMultiset[Int] + 1) + 1
     val c22 = (HashMultiset[Int] + 1) + 2

     "compute correct combinations" in {
       combinations(0, m1) must beEqual(new HashSet() + c0 )
       combinations(1, m1) must beEqual(new HashSet() + c0 + c11 + c12 )
       combinations(2, m1) must beEqual(new HashSet() + c0 + c11 + c12 + c21 + c22 )
       combinations(3, m1) must beEqual(new HashSet() + c0 + c11 + c12 + c21 + c22 + m1 )
     }
     "have correct foldLeft" in {
       m1.foldLeft(0)( (res, i) => res + i ) must beEqual(4)
     }
   }
}


