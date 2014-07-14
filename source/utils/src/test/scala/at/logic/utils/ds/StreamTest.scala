/*
 * StreamTest.scala
 */

package at.logic.utils.ds

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import streams.Definitions._

@RunWith(classOf[JUnitRunner])
class StreamTest extends SpecificationWithJUnit {

  "Stream utils" should {
    def from(n: Int) : Stream[Int] = Stream.cons(n, from( n + 1 ) )
    val nats = from(0)

    
    "have a correct even function" in {
      even(nats).take(10) must not (contain ( (n: Int) => n % 2 == 1 ))
    }  
    
    "have a correct odd function" in {
      odd(nats).take(10) must not (contain ( (n: Int) => n % 2 == 0 ))
    } 
  }
  
}
