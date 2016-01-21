package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.{ And, FOLAtom }
import org.specs2.mutable._

/**
 * Created by sebastian on 8/20/15.
 */
class ProofBuilderTest extends Specification {
  "ProofBuilder" should {
    val A = FOLAtom( "A", Nil )
    val B = FOLAtom( "B", Nil )
    val C = FOLAtom( "C", Nil )
    val D = FOLAtom( "D", Nil )
    val E = FOLAtom( "E", Nil )
    val F = FOLAtom( "F", Nil )

    "allow adding constant proofs" in {
      ( ProofBuilder
        c LogicalAxiom( A )
        c LogicalAxiom( B ) )
      success
    }

    "apply unary inferences" in {
      ( ProofBuilder
        c LogicalAxiom( A )
        u ( WeakeningLeftRule( _, B ) )
        u ( WeakeningRightRule( _, D ) ) )

      success
    }

    "apply binary inferences" in {
      ( ProofBuilder
        c LogicalAxiom( A )
        c LogicalAxiom( B )
        b ( AndRightRule( _, _, And( A, B ) ) ) )

      success
    }

    "return if there is only one proof on the stack" in {
      ( ProofBuilder
        c LogicalAxiom( A ) qed )
      success
    }
    "refuse to apply a unary inference to empty stack" in {
      ( ProofBuilder
        u ( WeakeningLeftRule( _, A ) ) ) must throwAn[Exception]
    }

    "refuse to apply a binary inference to stack with < 2 elements" in {
      ( ProofBuilder
        b ( AndRightRule( _, _, And( A, B ) ) ) ) must throwAn[Exception]

      ( ProofBuilder
        c LogicalAxiom( A )
        b ( AndRightRule( _, _, And( A, B ) ) ) ) must throwAn[Exception]
    }

    "refuse to return if there are too many or too few proofs on the stack" in {
      ( ProofBuilder qed ) must throwAn[Exception]
      ( ProofBuilder
        c LogicalAxiom( A )
        c LogicalAxiom( B ) qed ) must throwAn[Exception]
    }
  }
}
