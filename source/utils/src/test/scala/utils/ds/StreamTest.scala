/*
 * StreamTest.scala
 */

package at.logic.utils.ds

import org.specs._
import org.specs.runner._

import streams.Definitions._

class StreamTest extends SpecificationWithJUnit {
  "Stream utils" should {
    def from(n: Int) : Stream[Int] = Stream.cons(n, from( n + 1 ) )
    val nats = from(0)

    "have a correct even function" in {
      even(nats).take(10) must notExist( n => n % 2 == 1 )
    }  
    
    "have a correct odd function" in {
      odd(nats).take(10) must notExist( n => n % 2 == 0 )
    } 
  }
}
