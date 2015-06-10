package at.logic.gapt.provers.inductionProver

import at.logic.gapt.expr._
import at.logic.gapt.proofs.expansionTrees.{ ExpansionSequent, ETWeakQuantifier, merge, ETAtom }
import at.logic.gapt.provers.prover9.Prover9
import org.specs2.mutable._

class InductionProverTest extends Specification {

  if ( !Prover9.isInstalled ) skipAll

  "the SimpleInductionProof class" should {
    val zero = FOLConst( "0" )
    val alpha = FOLVar( "α" )
    val beta = FOLVar( "β" )
    val nu = FOLVar( "ν" )
    val gamma = FOLVar( "γ" )

    val x = FOLVar( "x" )
    val y = FOLVar( "y" )
    val z = FOLVar( "z" )
    val w = FOLVar( "w" )

    def s( x: FOLTerm ) = FOLFunction( "s", List( x ) )
    def m( x: FOLTerm, y: FOLTerm ) = FOLFunction( "*", x, y )
    def f( x: FOLTerm ) = FOLFunction( "f", List( x ) )
    def g( x: FOLTerm, y: FOLTerm ) = FOLFunction( "g", x, y )

    def f0 = Eq( f( zero ), s( zero ) )
    def fST( x: FOLTerm ) = Eq( f( s( x ) ), m( s( x ), f( x ) ) )
    def g0( x: FOLTerm ) = Eq( g( x, zero ), x )
    def gST( x: FOLTerm, y: FOLTerm ) = Eq( g( x, s( y ) ), g( m( x, s( y ) ), y ) )
    def uR( x: FOLTerm ) = Eq( m( x, s( zero ) ), x )
    def uL( x: FOLTerm ) = Eq( m( s( zero ), x ), x )
    def ASSO( x: FOLTerm, y: FOLTerm, z: FOLTerm ) = Eq( m( m( x, y ), z ), m( x, m( y, z ) ) )

    val F = Eq( g( gamma, nu ), m( gamma, f( nu ) ) )

    // Induction base

    val et1 = ETAtom( f0 )
    val et2 = merge( ETWeakQuantifier( All( x, g0( x ) ), List( ( ETAtom( g0( beta ) ), beta ) ) ) )
    val et3 = merge( ETWeakQuantifier( All( x, uR( x ) ), List( ( ETAtom( uR( beta ) ), beta ) ) ) )

    val ExpSeq0 = ExpansionSequent( List( et1, et2, et3 ), Nil )

    // Induction step

    val et4 = merge( ETWeakQuantifier( All( x, fST( x ) ), List( ( ETAtom( fST( nu ) ), nu ) ) ) )
    val et5 = merge( ETWeakQuantifier( All( x, All( z, gST( x, z ) ) ), List(
      ( ETWeakQuantifier( All( z, gST( gamma, z ) ), List(
        ( ETAtom( gST( gamma, nu ) ), nu ) ) ), gamma ) ) ) )
    val et6 = merge( ETWeakQuantifier( All( x, All( z, All( w, ASSO( x, z, w ) ) ) ), List(
      ( ETWeakQuantifier( All( z, All( w, ASSO( gamma, z, w ) ) ), List(
        ( ETWeakQuantifier( All( w, ASSO( gamma, s( nu ), w ) ), List(
          ( ETAtom( ASSO( gamma, s( nu ), f( nu ) ) ), f( nu ) ) ) ), s( nu ) ) ) ), gamma ) ) ) )

    val t = List( m( gamma, s( nu ) ) )

    val ExpSeq1 = ExpansionSequent( List( et4, et5, et6 ), Nil )

    // Conclusion

    val et7 = merge( ETWeakQuantifier( All( x, uL( x ) ), List(
      ( ETAtom( uL( f( alpha ) ) ), f( alpha ) ) ) ) )

    val et8 = ETAtom( Eq( g( s( zero ), alpha ), f( alpha ) ) )

    val u = List( s( zero ) )

    val ExpSeq2 = ExpansionSequent( List( et7 ), List( et8 ) )

    "be constructed correctly" in {
      val p = new SimpleInductionProof( ExpSeq0, ExpSeq1, ExpSeq2, t, u, F )

      success
    }

    "produce an LKProof" in {
      val p = new SimpleInductionProof( ExpSeq0, ExpSeq1, ExpSeq2, t, u, F )
      p.toLKProof

      success
    }
  }
}