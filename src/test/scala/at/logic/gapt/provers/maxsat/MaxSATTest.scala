/*
 * Tests for the MaxSAT interface.
**/

package at.logic.gapt.provers.maxsat

import at.logic.gapt.models.{ Interpretation, MapBasedInterpretation }
import at.logic.gapt.proofs.HOLClause
import org.specs2.mutable._

import at.logic.gapt.expr._
import org.specs2.specification.core.Fragment

class MaxSATTest extends Specification {
  val box: List[HOLClause] = List()

  /*
   * Simple instance for testing wether weighted partial MaxSAT
   * is called correctly and solves the instance.
   * Hard:
   *   x1 v x2
   *   x2 v x3
   *   x1 v x2 v x3
   * Soft: [minimizes the amount of variables to be true]
   *   -x1
   *   -x2
   *   -x3
   */
  object SimpleMaxSATFormula {
    val c1 = FOLConst( "c1" )
    val c2 = FOLConst( "c2" )
    val c3 = FOLConst( "c3" )

    val x1 = FOLAtom( "X", c1 :: Nil )
    val x2 = FOLAtom( "X", c2 :: Nil )
    val x3 = FOLAtom( "X", c3 :: Nil )

    val h1 = Or( x1, x2 )
    val h2 = Or( x2, x3 )
    val h3 = Or( Or( x1, x2 ), x3 )

    val s1 = ( Neg( x1 ), 1 )
    val s2 = ( Neg( x2 ), 1 )
    val s3 = ( Neg( x3 ), 1 )

    def apply() = {

      val hard = List( h1, h2, h3 )
      val soft = List( s1, s2, s3 )

      ( And( hard ), soft )
    }
  }

  def check( model: Option[Interpretation] ) = model must beLike {
    case Some( model ) =>
      model.interpret( SimpleMaxSATFormula.x2 ) must_== true
      model.interpret( SimpleMaxSATFormula.x1 ) must_== false
      model.interpret( SimpleMaxSATFormula.x3 ) must_== false
  }

  Fragment.foreach( Seq( QMaxSAT, ToySAT, ToySolver, MiniMaxSAT, MiFuMaX, OpenWBO ) ) { p =>
    p.getClass.getSimpleName should {
      "deal correctly with a simple instance" in {
        if ( !p.isInstalled ) skipped

        val ( hard, soft ) = SimpleMaxSATFormula()
        check( p.solve( hard, soft ) )
      }
    }
  }

  "MaxSat4j" should {

    "deal correctly with a simple instance" in {
      val ( hard, soft ) = SimpleMaxSATFormula()
      check( MaxSat4j.solve( hard, soft ) )
    }
  }
}
