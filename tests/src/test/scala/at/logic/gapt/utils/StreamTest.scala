/*
 * StreamTest.scala
 */

package at.logic.gapt.utils

import at.logic.gapt.utils.StreamUtils._
import org.specs2.mutable._

class StreamTest extends Specification {

  "Stream utils" should {
    def from( n: Int ): Stream[Int] = Stream.cons( n, from( n + 1 ) )
    val nats = from( 0 )

    "have a correct even function" in {
      even( nats ).take( 10 ) must not( contain( ( n: Int ) => n % 2 == 1 ) )
    }

    "have a correct odd function" in {
      odd( nats ).take( 10 ) must not( contain( ( n: Int ) => n % 2 == 0 ) )
    }
  }

}
