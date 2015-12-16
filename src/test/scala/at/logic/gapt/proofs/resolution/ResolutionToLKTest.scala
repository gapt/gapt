package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs._
import org.specs2.mutable._

class ResolutionToLKTest extends Specification {

  object UNSproof {
    val v0 = FOLVar( "v0" )
    val v1 = FOLVar( "v1" )
    val v2 = FOLVar( "v2" )

    val m01 = FOLFunction( "multiply", v0 :: v1 :: Nil )
    val m10 = FOLFunction( "multiply", v1 :: v0 :: Nil )
    val m02 = FOLFunction( "multiply", v0 :: v2 :: Nil )
    val m12 = FOLFunction( "multiply", v1 :: v2 :: Nil )
    val add01 = FOLFunction( "add", v0 :: v1 :: Nil )
    val am02m12 = FOLFunction( "add", m02 :: m12 :: Nil )
    val ma012 = FOLFunction( "multiply", add01 :: v2 :: Nil )
    val m2a01 = FOLFunction( "multiply", v2 :: add01 :: Nil )

    // =(multiply(v0, v1), multiply(v1, v0))
    val c1 = Eq( m01, m10 )
    // =(multiply(add(v0, v1), v2), add(multiply(v0, v2), multiply(v1, v2)))
    val c2 = Eq( ma012, am02m12 )
    // =(multiply(v2, add(v0, v1)), add(multiply(v0, v2), multiply(v1, v2)))
    val c3 = Eq( m2a01, am02m12 )

    val sub = FOLSubstitution( Map( ( v0, v2 ), ( v1, add01 ) ) )

    val p1 = InputClause( Clause() :+ c1 )
    val p2 = Instance( p1, sub )
    val p3 = InputClause( Clause() :+ c2 )
    val p4 = Paramodulation( p2, Suc( 0 ), p3, Suc( 0 ), c3 )

  }
  object UNSproofFreshvars {
    val v0 = FOLVar( "v0" )
    val v0u = FOLVar( "v0_" )
    val v1 = FOLVar( "v1" )
    val v1u = FOLVar( "v1_" )
    val v2 = FOLVar( "v2" )

    val m01u = FOLFunction( "multiply", v0u :: v1u :: Nil )
    val m10u = FOLFunction( "multiply", v1u :: v0u :: Nil )
    val m02 = FOLFunction( "multiply", v0 :: v2 :: Nil )
    val m12 = FOLFunction( "multiply", v1 :: v2 :: Nil )
    val add01 = FOLFunction( "add", v0 :: v1 :: Nil )
    val am02m12 = FOLFunction( "add", m02 :: m12 :: Nil )
    val ma012 = FOLFunction( "multiply", add01 :: v2 :: Nil )
    val m2a01 = FOLFunction( "multiply", v2 :: add01 :: Nil )

    // =(multiply(v0_, v1_), multiply(v1_, v0_))
    val c1 = Eq( m01u, m10u )
    // =(multiply(add(v0, v1), v2), add(multiply(v0, v2), multiply(v1, v2)))
    val c2 = Eq( ma012, am02m12 )
    // =(multiply(v2, add(v0, v1)), add(multiply(v0, v2), multiply(v1, v2)))
    val c3 = Eq( m2a01, am02m12 )

    val sub = FOLSubstitution( Map( ( v0, v2 ), ( v1, add01 ) ) )

    val p1 = InputClause( Clause() :+ c1 )
    val p2 = Instance( p1, sub )
    val p3 = InputClause( Clause() :+ c2 )
    val p4 = Paramodulation( p2, Suc( 0 ), p3, Suc( 0 ), c3 )
  }
  object UNSproofVariant {
    val v0 = FOLVar( "v0" )
    val v0u = FOLVar( "v0_" )
    val v1 = FOLVar( "v1" )
    val v1u = FOLVar( "v1_" )
    val v2 = FOLVar( "v2" )

    val m01 = FOLFunction( "multiply", v0 :: v1 :: Nil )
    val m10 = FOLFunction( "multiply", v1 :: v0 :: Nil )
    val m02 = FOLFunction( "multiply", v0 :: v2 :: Nil )
    val m12 = FOLFunction( "multiply", v1 :: v2 :: Nil )
    val add01 = FOLFunction( "add", v0 :: v1 :: Nil )
    val am02m12 = FOLFunction( "add", m02 :: m12 :: Nil )
    val ma012 = FOLFunction( "multiply", add01 :: v2 :: Nil )
    val m2a01 = FOLFunction( "multiply", v2 :: add01 :: Nil )

    // =(multiply(v0, v1), multiply(v1, v0))
    val c1 = Eq( m01, m10 )
    // =(multiply(add(v0, v1), v2), add(multiply(v0, v2), multiply(v1, v2)))
    val c2 = Eq( ma012, am02m12 )
    // =(multiply(v2, add(v0, v1)), add(multiply(v0, v2), multiply(v1, v2)))
    val c3 = Eq( m2a01, am02m12 )

    val sub1 = FOLSubstitution( Map( ( v0, v0u ), ( v1, v1u ) ) )
    val sub2 = FOLSubstitution( Map( ( v0u, v2 ), ( v1u, add01 ) ) )

    val p1 = InputClause( Clause() :+ c1 )
    val p1_ = Instance( p1, sub1 )
    val p2 = Instance( p1, sub2 )
    val p3 = InputClause( Clause() :+ c2 )
    val p4 = Paramodulation( p2, Suc( 0 ), p3, Suc( 0 ), c3 )

  }

  "RobinsonToLK" should {
    "transform the following resolution proof into an LK proof of the empty sequent" in {
      "containing only an initial clause" in {
        val Pa = FOLAtom( "P", FOLConst( "a" ) :: Nil )
        RobinsonToLK( TautologyClause( Pa ) ) must_== LogicalAxiom( Pa )
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

        val p1 = InputClause( Pfa +: Px +: Pfy +: Clause() )
        val resProof = Factor( Instance( p1, FOLSubstitution( x -> fa, y -> a ) ), Seq( Ant( 1 ), Ant( 0 ), Ant( 2 ) ) )._1

        val l1 = TheoryAxiom( Pfa +: Pfa +: Pfa +: Sequent() )
        val l2 = ContractionLeftRule( l1, Ant( 0 ), Ant( 1 ) )
        val lkProof = ContractionLeftRule( l2, Ant( 0 ), Ant( 1 ) )
        RobinsonToLK( resProof ) must_== lkProof
      }
      "containing a variant clause" in {
        val x = FOLVar( "x" )
        val y = FOLVar( "y" )
        val Px = FOLAtom( "P", x :: Nil )
        val Py = FOLAtom( "P", y :: Nil )

        val p1 = InputClause( Px +: Clause() )
        val resProof = Instance( p1, FOLSubstitution( x -> y ) )

        val lkProof = TheoryAxiom( Py +: Sequent() )
        RobinsonToLK( resProof ) must_== lkProof
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

        val p1 = InputClause( Px +: Clause() :+ Pfx )
        val p2 = InputClause( Pffa +: Clause() :+ Pfa )
        val resProof = Resolution( p2, Suc( 0 ), Instance( p1, FOLSubstitution( x -> fa ) ), Ant( 0 ) )

        val l1 = TheoryAxiom( Pfa +: Sequent() :+ Pffa )
        val l2 = TheoryAxiom( Pffa +: Sequent() :+ Pfa )
        val lkProof = CutRule( l2, Suc( 0 ), l1, Ant( 0 ) )
        RobinsonToLK( resProof ) must_== lkProof
      }
      "containing a paramodulation clause for rule 1" in {
        val a = FOLConst( "a" )
        val b = FOLConst( "b" )
        val x = FOLVar( "x" )
        val exb = Eq( x, b )
        val eab = Eq( a, b )
        val Pfa = FOLAtom( "P", FOLFunction( "f", a :: Nil ) :: Nil )
        val Pfb = FOLAtom( "P", FOLFunction( "f", b :: Nil ) :: Nil )

        val p1 = InputClause( Clause() :+ exb )
        val p2 = InputClause( Pfa +: Clause() )
        val resProof = Paramodulation( Instance( p1, FOLSubstitution( x -> a ) ), Suc( 0 ), p2, Ant( 0 ), Pfb )

        val l1 = TheoryAxiom( Sequent() :+ eab )
        val l2 = TheoryAxiom( Pfa +: Sequent() )
        val lkProof = ParamodulationLeftRule( l1, l1.conclusion( Suc( 0 ) ), l2, l2.conclusion( Ant( 0 ) ), Pfb )
        RobinsonToLK( resProof ) must_== lkProof
      }
      "containing a paramodulation clause for rule 2" in {
        val a = FOLConst( "a" )
        val b = FOLConst( "b" )
        val x = FOLVar( "x" )
        val ebx = Eq( b, x )
        val eba = Eq( b, a )
        val Pfa = FOLAtom( "P", FOLFunction( "f", a :: Nil ) :: Nil )
        val Pfb = FOLAtom( "P", FOLFunction( "f", b :: Nil ) :: Nil )

        val p1 = InputClause( Clause() :+ ebx )
        val p2 = InputClause( Pfa +: Clause() )
        val resProof = Paramodulation( Instance( p1, FOLSubstitution( x -> a ) ), Suc( 0 ), p2, Ant( 0 ), Pfb )

        val l1 = TheoryAxiom( Sequent() :+ eba )
        val l2 = TheoryAxiom( Pfa +: Sequent() )
        val lkProof = ParamodulationLeftRule( l1, l1.conclusion( Suc( 0 ) ), l2, l2.conclusion( Ant( 0 ) ), Pfb )
        RobinsonToLK( resProof ) must_== lkProof
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
        val p1 = InputClause( Clause() :+ Px )
        val p2 = InputClause( Pa +: Clause() )
        val v1 = Instance( p1, FOLSubstitution( x -> y ) )
        val resProof = Resolution( Instance( v1, FOLSubstitution( y -> a ) ), Suc( 0 ), p2, Ant( 0 ) )
        RobinsonToLK( resProof, seq ).endSequent must_== ( f1 +: Sequent() :+ Pa )
      }
      "transform the original subproof of the UNS example" in {
        RobinsonToLK( UNSproof.p4 ).endSequent must_== ( Sequent() :+ UNSproof.c3 )
      }
      "transform the subproof of the UNS example with unique variables" in {
        skipped( "does not work! fix!" )
        val r = RobinsonToLK( UNSproofFreshvars.p4 ).endSequent
        r.antecedent must beEmpty
        r.succedent.size mustEqual ( 1 )
        r.succedent( 0 ) mustEqual ( UNSproofFreshvars.c3 )
      }
      "transform the subproof of the UNS example with introduced variant" in {
        skipped( "does not work! fix!" )
        val r = RobinsonToLK( UNSproofVariant.p4 ).endSequent
        r.antecedent must beEmpty
        r.succedent.size mustEqual ( 1 )
        r.succedent( 0 ) mustEqual ( UNSproofVariant.c3 )
      }
    }
  }
}
