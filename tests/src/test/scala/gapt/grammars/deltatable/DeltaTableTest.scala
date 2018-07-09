package gapt.grammars.deltatable

import gapt.expr.{ FOLFunctionConst, Substitution, FOLConst, FOLVar }
import gapt.grammars.deltaTableAlgorithm
import org.specs2.mutable.Specification

class DeltaTableTest extends Specification {

  "key subsumption" should {
    val Seq( x1, x2, x3, x4 ) = 1 to 4 map { i => FOLVar( s"x$i" ) }
    val Seq( c1, c2, c3, c4 ) = 1 to 4 map { i => FOLConst( s"c$i" ) }

    "renaming" in {
      val k1 = Set(
        Substitution( x1 -> c1, x2 -> c2, x3 -> c3 ),
        Substitution( x1 -> c3, x2 -> c1, x3 -> c2 ) )
      val k2 = Set(
        Substitution( x1 -> c3, x2 -> c2, x3 -> c1 ),
        Substitution( x1 -> c1, x2 -> c3, x3 -> c2 ) )
      deltaTableAlgorithm.keySubsumption( k1, k2 ) must_== Set( Map( x1 -> x1, x2 -> x3, x3 -> x2 ) )
    }
  }

  "delta table creation" in {
    "many aus" in {
      val Seq( a, b, c, d ) = Seq( "a", "b", "c", "d" ) map { FOLConst( _ ) }
      val Seq( f, g ) = Seq( "f", "g" ) map { FOLFunctionConst( _, 3 ) }
      val lang = for {
        h <- Seq( f, g )
        t <- Seq(
          h( a, b, c ),
          h( b, c, a ),
          h( c, a, b ),
          h( c, d, a ),
          h( d, a, c ) )
      } yield t

      val table = deltaTableAlgorithm.createTable( lang.toSet )

      table must contain( atLeast( beLike[( Set[Substitution], deltaTableAlgorithm.Row )] {
        case ( s, decomps ) if s.size == 5 => ok
      } ) )
      ok
    }
  }

}
