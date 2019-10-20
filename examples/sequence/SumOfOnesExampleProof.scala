package sequence

import gapt.expr._
import gapt.examples.Formulas.CongUnaryEq
import gapt.examples.Formulas.Peano
import gapt.expr.formula.fol.FOLFunction
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.Utils
import gapt.proofs.Sequent
import gapt.proofs.gaptic.Proof
import gapt.proofs.gaptic.allL
import gapt.proofs.gaptic.impL
import gapt.proofs.gaptic.insert
import gapt.proofs.gaptic.prop
import gapt.proofs.gaptic.repeat
import gapt.proofs.gaptic.trivial
import gapt.proofs.lk.LKProof
import gapt.examples.Formulas.ReflexivityEq
import gapt.examples.Formulas.TransitivityEq

/**
 * Functions to construct cut-free FOL LK proofs of the sequents
 *
 * Refl, Trans, CongSuc, ABase, ASuc, :- sum( n ) = s^n^(0)
 *
 * where n is an Integer parameter >= 0.
 */
object SumOfOnesExampleProof extends ProofSequence {
  import Utils.{ numeral => num }

  def apply( n: Int ) = {
    val goal = if ( n == 0 ) foa"0 = 0" else foa"${sum( n )} = ${num( n )}"
    val endSequent = Sequent(
      Seq(
        "Refl" -> ReflexivityEq,
        "Trans" -> TransitivityEq,
        "CongSuc" -> CongUnaryEq( "s" ),
        "ABase" -> Peano.AdditionBase,
        "ASuc" -> Peano.AdditionSucc ), Seq(
        "Goal" -> goal ) )

    n match {
      case 0 | 1 =>
        Proof( endSequent ) {
          allL( "Refl", num( n ) )
          prop
        }

      case _ =>
        val subProof = apply( n - 1 )
        Proof( endSequent ) {
          allL( "CongSuc", sum( n - 1 ), num( n - 1 ) )
          impL( "CongSuc_0" )
          insert( subProof )

          allL( "Trans", sum( n ), FOLFunction( "s", sum( n - 1 ) ), num( n ) ) //Trans_0
          impL( "Trans_0" )
          insert( aux_proof( n - 1 ) )

          impL( "Trans_0" )
          repeat( trivial )
        }
    }
  }

  /** constructs proof of: Trans, CongSuc, ASuc, ABase :- sum( k + 1 ) = s( sum( k ) ) */
  private def aux_proof( n: Int ): LKProof = {
    val goal = fof"${sum( n + 1 )} = s(${sum( n )})"
    val endSequent = Sequent(
      Seq(
        "Trans" -> TransitivityEq,
        "CongSuc" -> CongUnaryEq( "s" ),
        "ABase" -> Peano.AdditionBase,
        "ASuc" -> Peano.AdditionSucc ), Seq(
        "Goal" -> goal ) )

    Proof( endSequent ) {
      allL( "ABase", sum( n ) ) //ABase_0
      allL( "ASuc", sum( n ), num( 0 ) ) // ASuc_0
      allL( "CongSuc", fot"${sum( n )} + 0", sum( n ) ) // CongSuc_0
      impL( "CongSuc_0" )
      trivial

      allL( "Trans", sum( n + 1 ), fot"s(${sum( n )} +0)", fot"s(${sum( n )})" ) // Trans_0
      impL( "Trans_0" )
      trivial

      impL( "Trans_0" )
      repeat( trivial )
    }
  }

  // the term (.((1 + 1) + 1 ) + ... + 1 ), k must be at least 1
  private def sum( k: Int ): FOLTerm = {
    if ( k == 1 ) Utils.numeral( 1 )
    else FOLFunction( "+", sum( k - 1 ) :: Utils.numeral( 1 ) :: Nil )
  }
}
