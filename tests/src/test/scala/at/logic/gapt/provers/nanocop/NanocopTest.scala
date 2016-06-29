package at.logic.gapt.provers.nanocop

import at.logic.gapt.examples.CountingEquivalence
import at.logic.gapt.formats.tptp.TptpParser
import at.logic.gapt.proofs.{ Sequent, SequentMatchers }
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class NanocopTest extends Specification with SatMatchers with SequentMatchers {

  args( skipAll = !NanoCoP.isInstalled )

  "counting 0" in {
    NanoCoP getExpansionProof CountingEquivalence( 0 ) must beLike {
      case Some( expansion ) =>
        expansion.deep must beValidSequent
        expansion.shallow must_== ( Sequent() :+ CountingEquivalence( 0 ) )
    }
  }

  "counting 1" in {
    NanoCoP getExpansionProof CountingEquivalence( 1 ) must beLike {
      case Some( expansion ) =>
        expansion.deep must beValidSequent
        expansion.shallow must_== ( Sequent() :+ CountingEquivalence( 1 ) )
    }
  }

  "alg211p1" in {
    val tptp = TptpParser.parseString( """
fof(basis_of, axiom, ![B,V]: (basis_of(B, V) => (lin_ind_subset(B, V) & a_subset_of(B, vec_to_class(V))))).
fof(bg_2_2_5, axiom, ![S,T,V]: ((lin_ind_subset(S, V) & basis_of(T, V)) => ?[U]: (a_subset_of(U, T) & basis_of(union(S, U), V)))).
fof(bg_remark_63_a, axiom, ![A]: (a_vector_space(A) => ?[B]: basis_of(B, A))).
fof(bg_2_4_a, axiom, ![A,B]: (a_vector_subspace_of(A, B) => a_vector_space(A))).
fof(bg_2_4_2, axiom, ![W,V,E]: ((a_vector_subspace_of(W, V) & a_subset_of(E, vec_to_class(W))) => (lin_ind_subset(E, W) <=> lin_ind_subset(E, V)))).
fof(bg_2_4_3, conjecture, ![W,V]: ((a_vector_subspace_of(W, V) & a_vector_space(V)) => ?[E,F]: (basis_of(union(E, F), V) & basis_of(E, W)))).
     """ ).toSequent
    NanoCoP getExpansionProof tptp must beLike {
      case Some( expansion ) =>
        expansion.deep must beValidSequent
        expansion.shallow must_== tptp
    }
  }

}
