package gapt.utils

import org.specs2.mutable.Specification

class UtilTests extends Specification {

  "symmetric closure should add missing pair" in {
    symmetricClosure( Set( 0 -> 1 ) ) must_== Set( 0 -> 1, 1 -> 0 )
  }

  "shortest path search" should {

    "find shortest path from 1 to 4" in {
      val edges = Set( 1 -> 2, 2 -> 3, 3 -> 4, 2 -> 4 )
      val weights: ( ( Int, Int ) => Int ) = {
        case ( 1, 2 ) => 1
        case ( 2, 3 ) => 1
        case ( 3, 4 ) => 1
        case ( 2, 4 ) => 3
      }
      shortestPath[Int]( 1, 4, edges, weights ) must beSome( Seq( 1, 2, 3, 4 ) )
    }

    "detect unreachable target" in {
      shortestPath[Int]( 1, 4, Set(), { case ( n, m ) => 1 } ) must beNone
    }
  }
}
