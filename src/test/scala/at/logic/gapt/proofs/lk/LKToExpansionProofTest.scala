package at.logic.gapt.proofs.lk

import at.logic.gapt.examples.LinearExampleProof
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Suc, Ant, Sequent }
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable._

class LKToExpansionProofTest extends Specification with SatMatchers {

  "The expansion tree extraction" should {

    "handle successive contractions " in {
      val etSeq = LKToExpansionProof( LinearExampleProof( 2 ) )
      toDeep( etSeq ) must beValidSequent
    }

    "do merge triggering a substitution triggering a merge" in {

      val alpha = Var( "\\alpha", Ti )
      val beta = Var( "\\beta", Ti )
      val c = Const( "c", Ti )
      val d = Const( "d", Ti )
      val f = Const( "f", Ti -> Ti )
      val x = Var( "x", Ti )
      val y = Var( "y", Ti )
      val z = Var( "z", Ti )
      val P = Const( "P", Ti -> To )
      val Q = Const( "Q", Ti -> ( Ti -> To ) )

      val p0 = Axiom(
        List( HOLAtom( P, alpha :: Nil ), HOLAtom( P, beta :: Nil ) ), // P(a), P(b)
        List( HOLAtom( Q, HOLFunction( f, alpha :: Nil ) :: c :: Nil ), HOLAtom( Q, HOLFunction( f, beta :: Nil ) :: d :: Nil ) )
      ) // Q(f(a), c), Q(f(b), d)
      val p1 = ExistsRightRule( p0, Ex( z, HOLAtom( Q, HOLFunction( f, alpha :: Nil ) :: z :: Nil ) ), c )
      val p2 = ExistsRightRule( p1, Ex( z, HOLAtom( Q, HOLFunction( f, beta :: Nil ) :: z :: Nil ) ), d )

      val p2_1 = ExistsRightRule( p2, Ex( y, Ex( z, HOLAtom( Q, y :: z :: Nil ) ) ), HOLFunction( f, alpha :: Nil ) )
      val p2_2 = ExistsRightRule( p2_1, Ex( y, Ex( z, HOLAtom( Q, y :: z :: Nil ) ) ), HOLFunction( f, beta :: Nil ) )

      val p2_3 = ContractionRightRule( p2_2, Ex( y, Ex( z, HOLAtom( Q, y :: z :: Nil ) ) ) )

      val p3 = ExistsLeftRule( p2_3, Ex( x, HOLAtom( P, x :: Nil ) ), alpha )
      val p4 = ExistsLeftRule( p3, Ex( x, HOLAtom( P, x :: Nil ) ), beta )
      val p5 = ContractionLeftRule( p4, Ex( x, HOLAtom( P, x :: Nil ) ) )

      val E = LKToExpansionProof( p5 ).expansionSequent

      E.antecedent mustEqual List( ETStrongQuantifier( Ex( x, HOLAtom( P, x :: Nil ) ), beta, ETAtom( HOLAtom( P, beta :: Nil ), false ) ) )
      // this assumes that the first variable wins, f(beta) would also be valid
      val f_alpha = HOLFunction( f, beta :: Nil )
      E.succedent mustEqual List( ETWeakQuantifier(
        Ex( y, Ex( z, HOLAtom( Q, y :: z :: Nil ) ) ),
        Map(
          f_alpha ->
            ETWeakQuantifier(
              Ex( z, HOLAtom( Q, f_alpha :: z :: Nil ) ),
              Map(
                c -> ETAtom( HOLAtom( Q, f_alpha :: c :: Nil ), true ),
                d -> ETAtom( HOLAtom( Q, f_alpha :: d :: Nil ), true )
              )
            )
        )
      ) )

    }

    "handle polarity" in {
      val p0 = WeakeningLeftRule( TopAxiom, Bottom() )
      val p1 = WeakeningRightRule( p0, Top() ) // weakened, hence bot on right side
      val p2 = ContractionRightRule( p1, Top() ) // polarity is positive, so bottom [merge] top = top
      val p3 = WeakeningLeftRule( p2, Bottom() ) // weakened, hence top on left side
      val p4 = ContractionLeftRule( p3, Bottom() ) // negative polarity, bottom must win

      toDeep( LKToExpansionProof( p4 ) ) must beValidSequent
    }

    "contractions on strong quantifiers" in {
      val Seq( x, y ) = Seq( "x", "y" ) map { FOLVar( _ ) }
      val p = FOLAtomConst( "p", 1 )

      val proof = ( ProofBuilder
        c LogicalAxiom( p( x ) )
        c LogicalAxiom( p( y ) )
        b ( OrLeftRule( _, Ant( 0 ), _, Ant( 0 ) ) )
        u ( ForallLeftBlock( _, All( x, All( y, p( x ) | p( y ) ) ), Seq( x, y ) ) )
        u ( ForallRightRule( _, All( x, p( x ) ), x ) )
        u ( ForallRightRule( _, All( x, p( x ) ), y ) )
        u ( ContractionRightRule( _, Suc( 0 ), Suc( 1 ) ) ) qed )

      val expansion = LKToExpansionProof( proof )

      toDeep( expansion ) must beValidSequent
    }

    "non-atomic initial sequents" in {
      val Seq( x, y ) = Seq( "x", "y" ) map { FOLVar( _ ) }
      val p = FOLAtomConst( "p", 2 )

      val proof = LogicalAxiom( All( x, Ex( y, p( x, y ) ) ) )
      val expansion = LKToExpansionProof( proof )

      toDeep( expansion ) must beValidSequent
    }
  }
}

