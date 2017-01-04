package at.logic.gapt.proofs.resolution

import at.logic.gapt.examples.{ BussTautology, CountingEquivalence }
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ naive, thresholds }
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs._
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable._

class ResolutionToLKTest extends Specification with SequentMatchers with SatMatchers {

  object UNSproof {
    val c1 = hof"multiply v0 v1 = multiply v1 v0"
    val c2 = hof"multiply (add v0 v1) v2 = add (multiply v0 v2) (multiply v1 v2)"
    val c3 = hof"multiply v2 (add v0 v1) = add (multiply v0 v2) (multiply v1 v2)"

    val sub = Substitution( hov"v0" -> le"v2", hov"v1" -> le"add v0 v1" )

    val p1 = Input( Clause() :+ c1 )
    val p2 = Subst( p1, sub )
    val p3 = Input( Clause() :+ c2 )
    val p4 = Paramod.withMain( p2, Suc( 0 ), p3, Suc( 0 ), c3 )
  }

  "ResolutionToLKProof" should {
    "transform the following resolution proof into an LK proof of the empty sequent" in {
      "containing only an initial clause" in {
        val Pa = FOLAtom( "P", FOLConst( "a" ) :: Nil )
        ResolutionToLKProof( Taut( Pa ) ) must_== LogicalAxiom( Pa )
      }
      "containing a factorized clause" in {
        val a = FOLConst( "a" )
        val x = FOLVar( "x" )
        val y = FOLVar( "y" )
        val fa = FOLFunction( "f", a :: Nil )
        val fy = FOLFunction( "f", y :: Nil )
        val Pfa = FOLAtom( "P", fa :: Nil )
        val Pfy = FOLAtom( "P", fy :: Nil )
        val Px = FOLAtom( "P", x :: Nil )

        val p1 = Input( Pfa +: Px +: Pfy +: Clause() )
        val resProof = Factor( Factor( Subst( p1, FOLSubstitution( x -> fa, y -> a ) ), Ant( 0 ), Ant( 1 ) ), Ant( 0 ), Ant( 1 ) )

        val l1 = TheoryAxiom( Pfa +: Pfa +: Pfa +: Sequent() )
        val l2 = ContractionLeftRule( l1, Ant( 0 ), Ant( 1 ) )
        val lkProof = ContractionLeftRule( l2, Ant( 0 ), Ant( 1 ) )
        ResolutionToLKProof.asDerivation( resProof ) must_== lkProof
      }
      "containing a variant clause" in {
        val x = FOLVar( "x" )
        val y = FOLVar( "y" )
        val Px = FOLAtom( "P", x :: Nil )
        val Py = FOLAtom( "P", y :: Nil )

        val p1 = Input( Px +: Clause() )
        val resProof = Subst( p1, FOLSubstitution( x -> y ) )

        val lkProof = TheoryAxiom( Py +: Sequent() )
        ResolutionToLKProof.asDerivation( resProof ) must_== lkProof
      }
      "containing a resolution clause" in {
        val x = FOLVar( "x" )
        val a = FOLConst( "a" )
        val fa = FOLFunction( "f", a :: Nil )
        val ffa = FOLFunction( "f", fa :: Nil )
        val fx = FOLFunction( "f", x :: Nil )
        val Px = FOLAtom( "P", x :: Nil )
        val Pfx = FOLAtom( "P", fx :: Nil )
        val Pfa = FOLAtom( "P", fa :: Nil )
        val Pffa = FOLAtom( "P", ffa :: Nil )

        val p1 = Input( Px +: Clause() :+ Pfx )
        val p2 = Input( Pffa +: Clause() :+ Pfa )
        val resProof = Resolution( p2, Suc( 0 ), Subst( p1, FOLSubstitution( x -> fa ) ), Ant( 0 ) )

        val l1 = TheoryAxiom( Pfa +: Sequent() :+ Pffa )
        val l2 = TheoryAxiom( Pffa +: Sequent() :+ Pfa )
        val lkProof = CutRule( l2, Suc( 0 ), l1, Ant( 0 ) )
        ResolutionToLKProof.asDerivation( resProof ) must_== lkProof
      }
      "containing a paramodulation clause for rule 1" in {
        val a = FOLConst( "a" )
        val b = FOLConst( "b" )
        val x = FOLVar( "x" )
        val exb = Eq( x, b )
        val eab = Eq( a, b )
        val Pfa = FOLAtom( "P", FOLFunction( "f", a :: Nil ) :: Nil )
        val Pfb = FOLAtom( "P", FOLFunction( "f", b :: Nil ) :: Nil )

        val p1 = Input( Clause() :+ exb )
        val p2 = Input( Pfa +: Clause() )
        val resProof = Paramod.withMain( Subst( p1, FOLSubstitution( x -> a ) ), Suc( 0 ), p2, Ant( 0 ), Pfb )

        val l1 = TheoryAxiom( Sequent() :+ eab )
        val l2 = TheoryAxiom( Pfa +: Sequent() )
        val lkProof = ParamodulationLeftRule( l1, l1.conclusion( Suc( 0 ) ), l2, l2.conclusion( Ant( 0 ) ), Pfb )
        ResolutionToLKProof.asDerivation( resProof ) must_== lkProof
      }
      "containing a paramodulation clause for rule 2" in {
        val a = FOLConst( "a" )
        val b = FOLConst( "b" )
        val x = FOLVar( "x" )
        val ebx = Eq( b, x )
        val eba = Eq( b, a )
        val Pfa = FOLAtom( "P", FOLFunction( "f", a :: Nil ) :: Nil )
        val Pfb = FOLAtom( "P", FOLFunction( "f", b :: Nil ) :: Nil )

        val p1 = Input( Clause() :+ ebx )
        val p2 = Input( Pfa +: Clause() )
        val resProof = Paramod.withMain( Subst( p1, FOLSubstitution( x -> a ) ), Suc( 0 ), p2, Ant( 0 ), Pfb )

        val l1 = TheoryAxiom( Sequent() :+ eba )
        val l2 = TheoryAxiom( Pfa +: Sequent() )
        val lkProof = ParamodulationLeftRule( l1, l1.conclusion( Suc( 0 ) ), l2, l2.conclusion( Ant( 0 ) ), Pfb )
        ResolutionToLKProof.asDerivation( resProof ) must_== lkProof
      }
    }
    "transform a resolution proof into an LK proof of the weakly quantified sequent" in {
      "∀xPx |-  Pa" in {
        val x = FOLVar( "x" )
        val y = FOLVar( "y" )
        val a = FOLConst( "a" )
        val Px = FOLAtom( "P", x :: Nil )
        val Pa = FOLAtom( "P", a :: Nil )
        val f1 = All( x, Px )

        val seq = HOLSequent( List( f1 ), List( Pa ) )
        val p1 = Input( Clause() :+ Px )
        val p2 = Input( Pa +: Clause() )
        val v1 = Subst( p1, FOLSubstitution( x -> y ) )
        val resProof = Resolution( Subst( v1, FOLSubstitution( y -> a ) ), Suc( 0 ), p2, Ant( 0 ) )
        ResolutionToLKProof( fixDerivation( resProof, seq ) ).endSequent must_== ( f1 +: Sequent() :+ Pa )
      }
      "transform the original subproof of the UNS example" in {
        ResolutionToLKProof.asDerivation( UNSproof.p4 ).endSequent must_== ( Sequent() :+ UNSproof.c3 )
      }
    }

    "transform rewriting at multiple positions" in {
      val proof = ResolutionToLKProof.asDerivation(
        Paramod(
          Input( Clause() :+ hoa"a = b" ), Suc( 0 ), true,
          Input( Clause() :+ hoa"p a a" ), Suc( 0 ),
          le"^x p x x: o"
        )
      )
      proof.endSequent must beMultiSetEqual( Sequent() :+ hoa"p b b" )
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

    "structural cnf with definitions" in {
      val Some( p ) = Escargot getLKProof BussTautology( 3 )
      p.conclusion must beMultiSetEqual( BussTautology( 3 ) )
    }
    "structural cnf 2" in {
      val as = 0 to 3 map { i => FOLAtom( s"a$i" ) }
      val endSequent = thresholds.exactly.oneOf( as ) +: Sequent() :+ naive.exactly.oneOf( as )
      val Some( p ) = Escargot getLKProof endSequent
      p.conclusion must beMultiSetEqual( endSequent )
    }

    "counting example" in {
      val Some( p ) = Escargot.getLKProof( CountingEquivalence( 1 ) )
      p.conclusion must_== ( Sequent() :+ CountingEquivalence( 1 ) )
    }
  }
}
