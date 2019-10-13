/*
 * StreamTest.scala
 */

package gapt.utils

import gapt.utils.StreamUtils._
import org.specs2.mutable._

class StreamTest extends Specification {

  "Stream utils" should {
    def from( n: Int ): LazyList[Int] = LazyList.cons( n, from( n + 1 ) )
    val nats = from( 0 )

    "have a correct even function" in {
      even( nats ).take( 10 ) must not( contain( ( n: Int ) => n % 2 == 1 ) )
    }

    "have a correct odd function" in {
      odd( nats ).take( 10 ) must not( contain( ( n: Int ) => n % 2 == 0 ) )
    }
  }

}
