package gapt.proofs.lk

import gapt.examples.{ LinearExampleProof, Pi2Pigeonhole, lattice }
import gapt.expr._
import gapt.expr.ty.TBase
import gapt.proofs.context.Context
import gapt.proofs.{ Ant, ProofBuilder, Sequent, SequentMatchers, Suc }
import gapt.proofs.expansion._
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.ContractionRightRule
import gapt.proofs.lk.rules.ConversionRightRule
import gapt.proofs.lk.rules.EqualityLeftRule
import gapt.proofs.lk.rules.EqualityRightRule
import gapt.proofs.lk.rules.ExistsLeftRule
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.ProofLink
import gapt.proofs.lk.rules.ReflexivityAxiom
import gapt.proofs.lk.rules.TopAxiom
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule
import gapt.proofs.lk.rules.macros.ForallLeftBlock
import gapt.proofs.lk.rules.macros.OrRightMacroRule
import gapt.proofs.lk.transformations.LKToExpansionProof
import gapt.utils.SatMatchers
import org.specs2.mutable._

class LKToExpansionProofTest extends Specification with SatMatchers with SequentMatchers {

  "The expansion tree extraction" should {

    "handle successive contractions " in {
      val etSeq = LKToExpansionProof( LinearExampleProof( 2 ) )
      etSeq.deep must beValidSequent
    }

    "do merge triggering a substitution triggering a merge" in {
      implicit var ctx = Context()
      ctx += TBase( "i" )
      ctx += hoc"P: i>o"
      ctx += hoc"Q: i>i>o"
      ctx += hoc"f: i>i"
      ctx += hoc"c: i"
      ctx += hoc"d: i"
      ctx += "ax" -> hcl"P α, P β :- Q (f α) c, Q (f β) d"

      val p = ProofBuilder.
        c( ProofLink( hoc"ax: i", hcl"P α, P β :- Q (f α) c, Q (f β) d" ) ).
        u( ExistsRightRule( _, hof"∃z Q (f α) z", le"c" ) ).
        u( ExistsRightRule( _, hof"∃z Q (f β) z", le"d" ) ).
        u( ExistsRightRule( _, hof"∃y ∃z Q y z", le"f α" ) ).
        u( ExistsRightRule( _, hof"∃y ∃z Q y z", le"f β" ) ).
        u( ContractionRightRule( _, hof"∃y ∃z Q y z" ) ).
        u( ExistsLeftRule( _, hof"∃x P x", fov"α" ) ).
        u( ExistsLeftRule( _, hof"∃x P x", fov"β" ) ).
        u( ContractionLeftRule( _, hof"∃x P x" ) ).
        qed

      val E = LKToExpansionProof( p ).expansionSequent

      E.antecedent must_== Seq( ExpansionTree( hof"∃x P x", Polarity.InAntecedent, ETtStrong( fov"α", ETtAtom ) ) )
      E.succedent must_== Seq( ExpansionTree( hof"∃y ∃z Q y z", Polarity.InSuccedent,
        // this assumes that the first variable wins, f(β) would also be valid
        ETtWeak( le"f α" -> ETtWeak( le"c" -> ETtAtom, le"d" -> ETtAtom ) ) ) )
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
      LKToExpansionProof( Pi2Pigeonhole.proof ).subProofs.foreach {
        case ETMerge( _, _ ) => ko
        case _               => ok
      }
      ok
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
      ctx += hof"P (x:i) = (x = x ∨ (¬ x = x))"

      val p = ProofBuilder.
        c( LogicalAxiom( fof"x = (x:i)" ) ).
        u( NegRightRule( _, Ant( 0 ) ) ).
        u( OrRightRule( _, Suc( 0 ), Suc( 1 ) ) ).
        u( ConversionRightRule( _, Suc( 0 ), fof"P(x)" ) ).
        u( OrRightMacroRule( _, fof"P(x)", fof"Q(x)" ) ).
        qed

      val e = LKToExpansionProof( p )

      ctx.check( e )
      ctx.check( p )

      e.deep must_== fos" :- x = x ∨ (¬ x = (x:i)) ∨ false"
    }

    "handle atom definitions in non-top position" in {
      implicit var ctx = Context()
      ctx += TBase( "i" )
      ctx += hoc"Q:i>o"
      ctx += hof"P (x:i) = (x = x ∨ (¬ x = (x:i)))"

      val p = ProofBuilder.
        c( LogicalAxiom( fof"x = (x:i)" ) ).
        u( NegRightRule( _, Ant( 0 ) ) ).
        u( OrRightRule( _, Suc( 0 ), Suc( 1 ) ) ).
        u( OrRightMacroRule( _, fof"x = (x:i) ∨ ¬ x = x", fof"Q(x)" ) ).
        u( ConversionRightRule( _, Suc( 0 ), fof"P(x) ∨ Q(x)" ) ).
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
        u( ConversionRightRule( _, Suc( 0 ), fof"h x = f (g x) ∨ ¬ f (g x) = f (g x)" ) ).
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
        u( ConversionRightRule( _, Suc( 0 ), hof"S P" ) ).
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
        u( ConversionRightRule( _, Suc( 0 ), hof"X -> n (n X)" ) ).
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
      exp.nonCutPart.shallow must beMultiSetEqual( lk.conclusion )
    }
  }
}

