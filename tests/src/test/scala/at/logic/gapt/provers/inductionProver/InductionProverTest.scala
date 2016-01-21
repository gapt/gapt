package at.logic.gapt.provers.inductionProver

import at.logic.gapt.expr._
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.proofs.expansion.{ ExpansionSequent, ETWeakQuantifier, ETAtom }
import org.specs2.mutable._

class InductionProverTest extends Specification {

  "the factorial example proof" should {
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

    val et1 = ETAtom( f0, false )
    val et2 = ETWeakQuantifier( All( x, g0( x ) ), Map( beta -> ETAtom( g0( beta ), false ) ) )
    val et3 = ETWeakQuantifier( All( x, uR( x ) ), Map( beta -> ETAtom( uR( beta ), false ) ) )

    val ExpSeq0 = ExpansionSequent( List( et1, et2, et3 ), Nil )

    // Induction step

    val et4 = ETWeakQuantifier( All( x, fST( x ) ), Map( nu -> ETAtom( fST( nu ), false ) ) )
    val et5 = ETWeakQuantifier( All( x, All( z, gST( x, z ) ) ), Map(
      gamma -> ETWeakQuantifier( All( z, gST( gamma, z ) ), Map(
        nu -> ETAtom( gST( gamma, nu ), false )
      ) )
    ) )
    val et6 = ETWeakQuantifier( All( x, All( z, All( w, ASSO( x, z, w ) ) ) ), Map(
      gamma -> ETWeakQuantifier( All( z, All( w, ASSO( gamma, z, w ) ) ), Map(
        s( nu ) -> ETWeakQuantifier( All( w, ASSO( gamma, s( nu ), w ) ), Map(
          f( nu ) -> ETAtom( ASSO( gamma, s( nu ), f( nu ) ), false )
        ) )
      ) )
    ) )

    val t = List( m( gamma, s( nu ) ) )

    val ExpSeq1 = ExpansionSequent( List( et4, et5, et6 ), Nil )

    // Conclusion

    val et7 = ETWeakQuantifier( All( x, uL( x ) ), Map( f( alpha ) -> ETAtom( uL( f( alpha ) ), false ) ) )

    val et8 = ETAtom( Eq( g( s( zero ), alpha ), f( alpha ) ), true )

    val u = List( s( zero ) )

    val ExpSeq2 = ExpansionSequent( List( et7 ), List( et8 ) )

    "be constructed correctly" in {
      val p = new SimpleInductionProof( ExpSeq0, ExpSeq1, ExpSeq2, t, u, F )

      success
    }

    "produce an LKProof" in {
      val p = new SimpleInductionProof( ExpSeq0, ExpSeq1, ExpSeq2, t, u, F )
      p.toLKProof( Escargot )

      success
    }

    "produce a SIP grammar" in {
      new SimpleInductionProof( ExpSeq0, ExpSeq1, ExpSeq2, t, u ).toSipGrammar

      success
    }

    "find the induction formula" in {
      val sip = new SimpleInductionProof( ExpSeq0, ExpSeq1, ExpSeq2, t, u )
      FindFormulaH( sip, 0, prover = Escargot ) must_== Some( m( gamma, f( nu ) ) === g( gamma, nu ) )
    }
  }

  "the associativity example proof" should {
    // Variables and constants
    val ( x, y, z ) = ( FOLVar( "x" ), FOLVar( "y" ), FOLVar( "z" ) )
    val ( alpha, beta, gamma ) = ( FOLVar( "α" ), FOLVar( "β" ), FOLVar( "γ" ) )
    val nu = FOLVar( "ν" )
    val zero = FOLConst( "0" )

    // Successor and addition
    def s( x: FOLTerm ) = FOLFunction( "s", List( x ) )

    def plus( x: FOLTerm, y: FOLTerm ) = FOLFunction( "+", List( x, y ) )

    // Instances of addition axioms
    def add0( v: FOLTerm ) = Eq( plus( v, zero ), v )

    def addS( u: FOLTerm, v: FOLTerm ) =
      Eq(
        plus( u, s( v ) ),
        s( plus( u, v ) )
      )

    // Instances of associativity and reflexivity
    def assoc( x: FOLTerm, y: FOLTerm, z: FOLTerm ) = Eq( plus( plus( x, y ), z ), plus( x, plus( y, z ) ) )
    def ref( t: FOLTerm ) = Eq( t, t )

    // Universally quantified equations
    val ForAllAssoc = All.Block( List( x, y, z ), assoc( x, y, z ) )
    val ForAllAdd0 = All( x, add0( x ) )
    val ForAllAddS = All.Block( List( x, y ), addS( x, y ) )

    val et1 = ETWeakQuantifier( ForAllAdd0, Map(
      beta -> ETAtom( add0( beta ), false ),
      plus( alpha, beta ) -> ETAtom( add0( plus( alpha, beta ) ), false )
    ) )

    val ExpSeq0 = ExpansionSequent( List( et1 ), Nil )

    val et2 = ETWeakQuantifier(
      ForAllAddS,
      Map(
        gamma ->
          ETWeakQuantifier(
            All( y, addS( gamma, y ) ),
            Map( nu -> ETAtom( addS( gamma, nu ), false ) )
          ),

        alpha ->
          ETWeakQuantifier(
            All( y, addS( alpha, y ) ),
            Map( plus( gamma, nu ) -> ETAtom( addS( alpha, plus( gamma, nu ) ), false ) )
          ),

        plus( alpha, gamma ) ->
          ETWeakQuantifier(
            All( y, addS( plus( alpha, gamma ), y ) ),
            Map( nu -> ETAtom( addS( plus( alpha, gamma ), nu ), false ) )
          )
      )
    )

    val t = List( gamma )

    val ExpSeq1 = ExpansionSequent( List( et2 ), Nil )

    val B = assoc( alpha, alpha, alpha )

    val u = List( alpha )

    val ExpSeq2 = ExpansionSequent( Nil, List( ETAtom( B, true ) ) )

    val F = assoc( alpha, gamma, nu )

    "be constructed correctly" in {
      val p = new SimpleInductionProof( ExpSeq0, ExpSeq1, ExpSeq2, t, u, F )

      success
    }

    "produce an LKProof" in {
      val p = new SimpleInductionProof( ExpSeq0, ExpSeq1, ExpSeq2, t, u, F )
      p.toLKProof( Escargot )

      success
    }

    "produce a SIP grammar" in {
      new SimpleInductionProof( ExpSeq0, ExpSeq1, ExpSeq2, t, u ).toSipGrammar

      success
    }

    "find the induction formula" in {
      val sip = new SimpleInductionProof( ExpSeq0, ExpSeq1, ExpSeq2, t, u )
      FindFormulaH( sip, 0, prover = Escargot ) must_== Some( assoc( alpha, gamma, nu ) )
    }
  }
}