package at.logic.gapt.proofs.lk

import at.logic.gapt.examples.{ LinearExampleProof, Pi2Pigeonhole, lattice }
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Ant, Context, Sequent, SequentMatchers, Suc }
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable._

class LKToExpansionProofTest extends Specification with SatMatchers with SequentMatchers {

  "The expansion tree extraction" should {

    "handle successive contractions " in {
      val etSeq = LKToExpansionProof( LinearExampleProof( 2 ) )
      etSeq.deep must beValidSequent
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

      E.antecedent mustEqual List( ETStrongQuantifier( Ex( x, HOLAtom( P, x :: Nil ) ), beta, ETAtom( HOLAtom( P, beta :: Nil ), Polarity.InAntecedent ) ) )
      // this assumes that the first variable wins, f(beta) would also be valid
      val f_alpha = HOLFunction( f, beta :: Nil )
      E.succedent mustEqual List( ETWeakQuantifier(
        Ex( y, Ex( z, HOLAtom( Q, y :: z :: Nil ) ) ),
        Map(
          f_alpha ->
            ETWeakQuantifier(
              Ex( z, HOLAtom( Q, f_alpha :: z :: Nil ) ),
              Map(
                c -> ETAtom( HOLAtom( Q, f_alpha :: c :: Nil ), Polarity.InSuccedent ),
                d -> ETAtom( HOLAtom( Q, f_alpha :: d :: Nil ), Polarity.InSuccedent )
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

      LKToExpansionProof( p4 ).deep must beValidSequent
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

      expansion.deep must beValidSequent
    }

    "non-atomic initial sequents" in {
      val Seq( x, y ) = Seq( "x", "y" ) map { FOLVar( _ ) }
      val p = FOLAtomConst( "p", 2 )

      val proof = LogicalAxiom( All( x, Ex( y, p( x, y ) ) ) )
      val expansion = LKToExpansionProof( proof )

      expansion.deep must beValidSequent
    }

    "return merge-free proofs" in {
      LKToExpansionProof( Pi2Pigeonhole.proof ).subProofs must not( contain( beAnInstanceOf[ETMerge] ) )
    }

    "equality on weakened formulas" in {
      val proof = ( ProofBuilder
        c ReflexivityAxiom( le"t" )
        u ( WeakeningLeftRule( _, hof"t=s" ) )
        u ( EqualityRightRule( _, eq = hof"t=s", aux = hof"t=t", mainFormula = hof"s=t" ) ) qed )

      LKToExpansionProof( proof ).deep must beEValidSequent
    }

    "replacement contexts" in {
      val lk = ( ProofBuilder c ReflexivityAxiom( le"c" )
        u ( ExistsRightRule( _, hof"∃x x=c", le"c" ) )
        u ( WeakeningLeftRule( _, hof"c=d" ) )
        u ( EqualityRightRule( _, Ant( 0 ), Suc( 0 ), le"λx ∃y y=x".asInstanceOf[Abs] ) ) qed )
      LKToExpansionProof( lk ).shallow must_== lk.conclusion
    }

    "equation left rule" in {
      val lk = ProofBuilder.
        c( LogicalAxiom( hof"a=b" ) ).
        u( WeakeningLeftRule( _, hof"b=c" ) ).
        u( EqualityLeftRule( _, hof"a=b", hof"b=c", hof"a=c" ) ).
        qed
      LKToExpansionProof( lk ).shallow must_== lk.conclusion
    }

    "handle atom definitions in top position" in {
      implicit var ctx = Context()
      ctx += TBase( "i" )
      ctx += hoc"Q: i>o"
      ctx += hof"P x = (x = x ∨ (¬ x = x))"

      val p = ProofBuilder.
        c( LogicalAxiom( fof"x = x" ) ).
        u( NegRightRule( _, Ant( 0 ) ) ).
        u( OrRightRule( _, Suc( 0 ), Suc( 1 ) ) ).
        u( DefinitionRightRule( _, Suc( 0 ), fof"P(x)" ) ).
        u( OrRightMacroRule( _, fof"P(x)", fof"Q(x)" ) ).
        qed

      val e = LKToExpansionProof( p )

      ctx.check( e )
      ctx.check( p )

      e.deep must_== fos" :- x = x ∨ (¬ x = x) ∨ false"
    }

    "handle atom definitions in non-top position" in {
      implicit var ctx = Context()
      ctx += TBase( "i" )
      ctx += hoc"Q:i>o"
      ctx += hof"P x = (x = x ∨ (¬ x = x))"

      val p = ProofBuilder.
        c( LogicalAxiom( fof"x = x" ) ).
        u( NegRightRule( _, Ant( 0 ) ) ).
        u( OrRightRule( _, Suc( 0 ), Suc( 1 ) ) ).
        u( OrRightMacroRule( _, fof"x = x ∨ ¬ x = x", fof"Q(x)" ) ).
        u( DefinitionRightRule( _, Suc( 0 ), fof"P(x) ∨ Q(x)" ) ).
        qed

      val e = LKToExpansionProof( p )

      ctx.check( p )
      ctx.check( e )

      e.shallow must_== hos" :- P(x) ∨ Q(x)"
    }

    "handle term definitions" in {
      implicit var ctx = Context()
      ctx += TBase( "i" )
      ctx += hoc"f: i>i"
      ctx += hoc"g: i>i"
      ctx += hof"h x = f (g x)"

      val p = ProofBuilder.
        c( LogicalAxiom( fof"f( g x) = f (g x)" ) ).
        u( NegRightRule( _, Ant( 0 ) ) ).
        u( OrRightRule( _, Suc( 0 ), Suc( 1 ) ) ).
        u( DefinitionRightRule( _, Suc( 0 ), fof"h x = f (g x) ∨ ¬ f (g x) = f (g x)" ) ).
        qed

      val e = LKToExpansionProof( p )

      ctx.check( p )
      ctx.check( e )

      e.shallow must_== fos":- h x = f (g x) ∨ ¬ f(g x) = f (g x)"
    }

    "work on a simple example of a term definition of type o" in {
      implicit var ctx = Context()
      ctx += hoc"Q: o"
      ctx += hoc"R: o"
      ctx += hoc"S: o >o"
      ctx += hof"P = (Q & R)"

      val p = ProofBuilder.
        c( LogicalAxiom( hof"S(Q & R)" ) ).
        u( DefinitionRightRule( _, Suc( 0 ), hof"S P" ) ).
        qed

      val e = LKToExpansionProof( p )

      ctx.check( p )
      ctx.check( e )

      e.shallow must_== hos"S(Q & R) :- S(P)"
    }

    "fail on double negation definition example" in {
      implicit var ctx = Context()
      ctx += hof"n X = (-X)"

      val p = ProofBuilder.
        c( LogicalAxiom( hoa"X" ) ).
        u( NegLeftRule( _, Suc( 0 ) ) ).
        u( NegRightRule( _, Ant( 0 ) ) ).
        u( ImpRightRule( _, Ant( 0 ), Suc( 0 ) ) ).
        u( DefinitionRightRule( _, Suc( 0 ), hof"X -> n (n X)" ) ).
        qed

      val e = LKToExpansionProof( p )

      ctx.check( p )
      ctx.check( e )

      e.shallow must_== hos":- X -> n (n X)"
    }

    "lattice with definitions" in {
      import lattice._
      val exp = LKToExpansionProof( lattice.p )
      val Right( lk ) = ExpansionProofToLK.withTheory( implicitly )( exp )
      ctx.check( exp )
      ctx.check( lk )
      exp.shallow must beMultiSetEqual( lk.conclusion )
    }
  }
}

