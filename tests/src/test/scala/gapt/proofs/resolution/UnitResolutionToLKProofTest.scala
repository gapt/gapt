package gapt.proofs.resolution

import gapt.expr._
import gapt.proofs.{ Ant, Sequent, Suc, RichFormulaSequent }
import org.specs2.mutable.Specification

class UnitResolutionToLKProofTest extends Specification {

  "flips" in {
    val p1 = Input( Sequent() :+ hof"a=b" )
    val p2 = Input( hof"b=a" +: Sequent() )

    UnitResolutionToLKProof( Resolution( Flip( p1, Suc( 0 ) ), p2, hof"b=a" ) ).conclusion.toImplication must_== hof"a=b -> b=a"
    UnitResolutionToLKProof( Resolution( p1, Flip( p2, Ant( 0 ) ), hof"a=b" ) ).conclusion.toImplication must_== hof"a=b -> b=a"
  }

  "double flip" in {
    val p1 = Input( Sequent() :+ hof"a=b" )
    val p2 = Input( hof"a=b" +: Sequent() )

    UnitResolutionToLKProof( Resolution( Flip( p1, Suc( 0 ) ), Flip( p2, Ant( 0 ) ), hof"b=a" ) ).conclusion.toImplication must_== hof"a=b -> a=b"
  }

}
