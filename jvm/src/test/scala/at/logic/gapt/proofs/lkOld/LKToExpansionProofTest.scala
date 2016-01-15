package at.logic.gapt.proofs.lkOld

import at.logic.gapt.examples.LinearExampleProof
import at.logic.gapt.proofs.lk.lkNew2Old
import org.specs2.mutable._
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.Utils
import at.logic.gapt.proofs.expansionTrees._

class ExtractExpansionSequentTest extends Specification {

  "The expansion tree extraction" should {

    "handle successive contractions " in {
      val etSeq = LKToExpansionProof( lkNew2Old( LinearExampleProof( 2 ) ) )

      val p = "P"
      val x = FOLVar( "x" )
      val s = "s"

      val ass = All( x, Imp( FOLAtom( p, x :: Nil ), FOLAtom( p, FOLFunction( s, x :: Nil ) :: Nil ) ) )

      val equal_permut_1 = etSeq.antecedent equals List(
        ETAtom( FOLAtom( p, Utils.numeral( 0 ) :: Nil ) ),
        ETWeakQuantifier( ass, List(
          ( ETImp( ETAtom( FOLAtom( p, Utils.numeral( 0 ) :: Nil ) ), ETAtom( FOLAtom( p, Utils.numeral( 1 ) :: Nil ) ) ), Utils.numeral( 0 ) ),
          ( ETImp( ETAtom( FOLAtom( p, Utils.numeral( 1 ) :: Nil ) ), ETAtom( FOLAtom( p, Utils.numeral( 2 ) :: Nil ) ) ), Utils.numeral( 1 ) )
        ) )
      )

      val equal_permut_2 = etSeq.antecedent equals List(
        ETAtom( FOLAtom( p, Utils.numeral( 0 ) :: Nil ) ),
        ETWeakQuantifier( ass, List(
          ( ETImp( ETAtom( FOLAtom( p, Utils.numeral( 1 ) :: Nil ) ), ETAtom( FOLAtom( p, Utils.numeral( 2 ) :: Nil ) ) ), Utils.numeral( 1 ) ),
          ( ETImp( ETAtom( FOLAtom( p, Utils.numeral( 0 ) :: Nil ) ), ETAtom( FOLAtom( p, Utils.numeral( 1 ) :: Nil ) ) ), Utils.numeral( 0 ) )
        ) )
      )

      ( equal_permut_1 || equal_permut_2 ) must beTrue

      etSeq.succedent mustEqual ( List( ETAtom( FOLAtom( p, Utils.numeral( 2 ) :: Nil ) ) ) )
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
      val p1 = ExistsRightRule( p0, HOLAtom( Q, HOLFunction( f, alpha :: Nil ) :: c :: Nil ), Ex( z, HOLAtom( Q, HOLFunction( f, alpha :: Nil ) :: z :: Nil ) ), c )
      val p2 = ExistsRightRule( p1, HOLAtom( Q, HOLFunction( f, beta :: Nil ) :: d :: Nil ), Ex( z, HOLAtom( Q, HOLFunction( f, beta :: Nil ) :: z :: Nil ) ), d )

      val p2_1 = ExistsRightRule( p2, Ex( z, HOLAtom( Q, HOLFunction( f, alpha :: Nil ) :: z :: Nil ) ), Ex( y, Ex( z, HOLAtom( Q, y :: z :: Nil ) ) ), HOLFunction( f, alpha :: Nil ) )
      val p2_2 = ExistsRightRule( p2_1, Ex( z, HOLAtom( Q, HOLFunction( f, beta :: Nil ) :: z :: Nil ) ), Ex( y, Ex( z, HOLAtom( Q, y :: z :: Nil ) ) ), HOLFunction( f, beta :: Nil ) )

      val p2_3 = ContractionRightRule( p2_2, Ex( y, Ex( z, HOLAtom( Q, y :: z :: Nil ) ) ) )

      val p3 = ExistsLeftRule( p2_3, HOLAtom( P, alpha :: Nil ), Ex( x, HOLAtom( P, x :: Nil ) ), alpha )
      val p4 = ExistsLeftRule( p3, HOLAtom( P, beta :: Nil ), Ex( x, HOLAtom( P, x :: Nil ) ), beta )
      val p5 = ContractionLeftRule( p4, Ex( x, HOLAtom( P, x :: Nil ) ) )

      val ( ante, succ ) = LKToExpansionProof( p5 ).toTuple

      ante mustEqual ( List( ETStrongQuantifier( Ex( x, HOLAtom( P, x :: Nil ) ), alpha, ETAtom( HOLAtom( P, alpha :: Nil ) ) ) ) )
      // this assumes that the first variable wins, f(beta) would also be valid
      val f_alpha = HOLFunction( f, alpha :: Nil )
      succ mustEqual ( List( ETWeakQuantifier(
        Ex( y, Ex( z, HOLAtom( Q, y :: z :: Nil ) ) ),
        List(
          (
            ETWeakQuantifier(
              Ex( z, HOLAtom( Q, f_alpha :: z :: Nil ) ),
              List(
                ( ETAtom( HOLAtom( Q, f_alpha :: c :: Nil ) ), c ),
                ( ETAtom( HOLAtom( Q, f_alpha :: d :: Nil ) ), d )
              )
            ),
              f_alpha
          )
        )
      ) ) )

    }

    "handle polarity" in {
      val p0 = Axiom( Bottom() :: Nil, Top() :: Nil )
      val p1 = WeakeningRightRule( p0, Top() ) // weakened, hence bot on right side
      val p2 = ContractionRightRule( p1, Top() ) // polarity is positive, so bottom [merge] top = top
      val p3 = WeakeningLeftRule( p2, Bottom() ) // weakened, hence top on left side
      val p4 = ContractionLeftRule( p3, Bottom() ) // negative polarity, bottom must win

      val ( ante, succ ) = LKToExpansionProof( p4 ).toTuple
      ante mustEqual ETBottom :: Nil
      succ mustEqual ETTop :: Nil
    }

    "handle multiple formulas in axiom" in {
      val s = "s"
      val c = FOLConst( "c" )
      val d = FOLConst( "d" )
      val x = FOLVar( "x" )
      val p = "P"

      val f = All( x, FOLAtom( p, x :: Nil ) )

      val p0_0 = Axiom( FOLAtom( p, c :: Nil ) :: f :: Nil, FOLAtom( p, c :: Nil ) :: Nil )

      val p0_1 = Axiom( FOLAtom( p, d :: Nil ) :: Nil, FOLAtom( p, d :: Nil ) :: Nil )
      val p0_2 = ForallLeftRule( p0_1, FOLAtom( p, d :: Nil ), f, d )

      val p1 = AndRightRule( p0_0, p0_2, FOLAtom( p, c :: Nil ), FOLAtom( p, d :: Nil ) )
      val p2 = ContractionLeftRule( p1, f )

      val etSeq = LKToExpansionProof( p2 )

      etSeq.antecedent.count( _.isInstanceOf[ETWeakQuantifier] ) mustEqual 1
      etSeq.antecedent.count( _.isInstanceOf[ETAtom] ) mustEqual 1
    }
  }
}

