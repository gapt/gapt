
package at.logic.gapt.proofs.shlk.algorithms

import at.logic.gapt.expr._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.algorithms.solve
import at.logic.gapt.proofs.lk.base.FSequent
import org.junit.runner.RunWith
import org.specs2.execute.Success
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner

// Seems like this is testing auto-propositional for HOL... why is it here?
@RunWith( classOf[JUnitRunner] )
class BussGeneratorAutoPropTest extends SpecificationWithJUnit {
  "BussGeneratorAutoPropTest" should {
    "continue autopropositional" in {

      val a = Const( "a", Ti )

      val Pc1 = HOLAtom( Const( "Pc1", Ti -> To ), a :: Nil )
      val Pc2 = HOLAtom( Const( "Pc2", Ti -> To ), a :: Nil )
      val Pd1 = HOLAtom( Const( "Pd1", Ti -> To ), a :: Nil )
      val Pd2 = HOLAtom( Const( "Pd2", Ti -> To ), a :: Nil )
      val Pc1_or_Pd1 = Or( Pc1, Pd1 )
      val imp_Pc1_or_Pd1_Pc2 = Imp( Pc1_or_Pd1, Pc2 )
      val imp_Pc1_or_Pd1_Pd2 = Imp( Pc1_or_Pd1, Pd2 )
      val imp_Pc1_or_Pd1_Pc2__or__imp_Pc1_or_Pd1_Pd2 = Or( imp_Pc1_or_Pd1_Pc2, imp_Pc1_or_Pd1_Pd2 )
      //      val fs = FSequent(imp_Pc1_or_Pd1_Pc2__or__imp_Pc1_or_Pd1_Pd2 :: Pc1_or_Pd1 :: Nil , Pc2::Pd2::Nil)
      val fs = BussTautology( 2 )
      val bussGen = solve.solvePropositional( fs )

      Success()
    }
  }
}

object BussTautology {
  def apply( n: Int ): FSequent = FSequent( Ant( n ), c( n ) :: d( n ) :: Nil )

  val a = Const( "a", Ti )

  def c( i: Int ) = HOLAtom( Const( "c_" + i, Ti -> To ), a :: Nil )
  def d( i: Int ) = HOLAtom( Const( "d_" + i, Ti -> To ), a :: Nil )
  def F( i: Int ): HOLFormula = if ( i == 1 )
    Or( c( 1 ), d( 1 ) )
  else
    And( F( i - 1 ), Or( c( i ), d( i ) ) )
  def A( i: Int ) = if ( i == 1 ) c( 1 )
  else Imp( F( i - 1 ), c( i ) )
  def B( i: Int ) = if ( i == 1 ) d( 1 )
  else Imp( F( i - 1 ), d( i ) )

  // the antecedens of the final sequent
  def Ant( i: Int ): List[HOLFormula] = if ( i == 0 ) Nil else Or( A( i ), B( i ) ) :: Ant( i - 1 )
}
