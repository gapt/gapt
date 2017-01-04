package at.logic.gapt.proofs.resolution

import at.logic.gapt.examples.CountingEquivalence
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ naive, thresholds }
import at.logic.gapt.expr.hol.CNFn
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.proofs.{ Sequent, SequentMatchers }
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable._

class ResolutionToExpansionProofTest extends Specification with SatMatchers with SequentMatchers {
  "simple proof from prover9" should {
    val es = (
      hof"!z P(c,z)" +:
      hof"!x!y!z (P(x,g(z)) -> P(f(x),z) & R(y))" +:
      hof"!x!z (P(x,z) -> Q(x))" +:
      Sequent()
      :+ hof"?x Q(f(f(x)))"
    )

    "extract expansion sequent" in {
      val Some( robinson ) = Escargot getResolutionProof es
      val expansion = ResolutionToExpansionProof( robinson )
      expansion.deep must beValidSequent
    }
  }

  "tautological clauses with naive CNF" in {
    val p = FOLAtom( "p" )
    val endSequent = Sequent() :+ ( ( p --> -( -p ) ) & ( -( -p ) --> p ) )
    val cnf = CNFn( endSequent.toDisjunction )
    val Some( robinson ) = Escargot getResolutionProof cnf
    val expansion = ResolutionToExpansionProof( fixDerivation( robinson, endSequent ) )
    expansion.shallow must_== endSequent
    expansion.deep must beValidSequent
  }

  "complicated formula with structural CNF" in {
    val x = FOLVar( "x" )
    val Seq( c, d ) = Seq( "c", "d" ) map { FOLConst( _ ) }
    val as = ( 0 to 12 ) map { i => FOLAtomConst( s"a$i", 1 ) }
    val endSequent = thresholds.atMost.oneOf( as map { a => Ex( x, a( x ) ) } ) +: Sequent() :+ ( as( 0 )( c ) --> -as( 1 )( d ) )

    val Some( ref ) = Escargot getResolutionProof endSequent
    val expansion = ResolutionToExpansionProof( ref )
    expansion.shallow must_== endSequent
    expansion.deep must beValidSequent
  }

  "quantified definitions" in {
    val endSequent = Sequent() :+ CountingEquivalence( 2 )

    val Some( ref ) = Escargot getResolutionProof endSequent
    val expansion = ResolutionToExpansionProof( ref )
    expansion.shallow must_== endSequent
    expansion.deep must beValidSequent
  }

  "duplicate bound variables" in {
    val Seq( p, q ) = Seq( "p", "q" ) map { FOLAtomConst( _, 1 ) }
    val Seq( c, d ) = Seq( "c", "d" ) map { FOLConst( _ ) }
    val x = FOLVar( "x" )

    val endSequent = Sequent() :+ ( ( All( x, p( x ) ) | All( x, q( x ) ) ) --> ( p( c ) | q( d ) ) )

    val Some( ref ) = Escargot getResolutionProof endSequent
    val expansion = ResolutionToExpansionProof( ref )
    expansion.shallow must_== endSequent
    expansion.deep must beValidSequent
  }
}
