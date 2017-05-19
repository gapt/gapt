import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.prooftool.prooftool

// Example 0.1.6
object ex0_1_6 extends Script {
  val s1 = LogicalAxiom( hof"A" )
  val s2 = WeakeningLeftRule( s1, hof"B" )
  val s3 = WeakeningRightRule( s2, hof"B" )
  val s4 = ImpRightRule( s3, hof"A -> B" )
  val s5 = ImpRightRule( s4, hof"B -> A" )
  val s6 = WeakeningRightRule( s5, hof"A -> B" )
  val s7 = WeakeningRightRule( s6, hof"B -> A" )
  val s8 = OrRightRule( s7, hof"(A -> B) | (B -> A)" )
  val s9 = OrRightRule( s8, hof"(A -> B) | (B -> A)" )
  val s10 = ContractionRightRule( s9, hof"(A -> B) | (B -> A)" )

  println( s10 )

  val nd = LKToND( s10 )
  println( nd )
}

// Example 0.1.6 short
object ex0_1_6_short extends Script {
  val s1 = LogicalAxiom( hof"A" )
  val s2 = WeakeningLeftRule( s1, hof"B" )
  val s3 = WeakeningRightRule( s2, hof"B" )
  val s4 = ImpRightRule( s3, hof"A -> B" )
  val s5 = ImpRightRule( s4, hof"B -> A" )
  val s6 = OrRightRule( s5, hof"(A -> B) | (B -> A)" )

  println( s6 )

  val nd = LKToND( s6 )
  println( "ex0_1_6_short" )
  println( nd )

  //prooftool( nd )
}

object demorgan1 extends Script {
  val s1 = LogicalAxiom( hof"A" )
  val s2 = WeakeningRightRule( s1, hof"B" )
  val s3 = OrRightRule( s2, hof"A | B" )
  val s4 = NegLeftRule( s3, hof"A | B" )
  val s5 = NegRightRule( s4, hof"A" )

  val r1 = LogicalAxiom( hof"B" )
  val r2 = WeakeningRightRule( r1, hof"A" )
  val r3 = OrRightRule( r2, hof"A | B" )
  val r4 = NegLeftRule( r3, hof"A | B" )
  val r5 = NegRightRule( r4, hof"B" )

  val p1 = AndRightRule( s5, r5, hof"-A & -B" )
  val p2 = ContractionLeftRule( p1, hof"-(A | B)" )
  println( p2 )

  val nd = LKToND( p2 )
  println( nd )
}

object demorgan2 extends Script {
  val s1 = LogicalAxiom( hof"A" )
  val s2 = NegLeftRule( s1, hof"A" )
  val s3 = WeakeningLeftRule( s2, hof"B" )

  val r1 = LogicalAxiom( hof"B" )
  val r2 = NegLeftRule( r1, hof"B" )
  val r3 = WeakeningLeftRule( r2, hof"A" )

  val p1 = OrLeftRule( s3, r3, hof"-A | -B" )
  val p2 = ContractionLeftRule( p1, hof"A" )
  val p3 = ContractionLeftRule( p2, hof"B" )
  val p4 = AndLeftRule( p3, hof"A & B" )
  val p5 = NegRightRule( p4, hof"A & B" )
  println( p5 )

  val nd = LKToND( p5 )
  println( nd )
}

object orLeft1 extends Script {
  val l1 = LogicalAxiom( hof"A" )
  val r1 = LogicalAxiom( hof"B" )
  val p = OrLeftRule( l1, r1, hof"A | B" )
  println( p )

  val nd = LKToND( p )
  println( nd )
}

object orLeft2 extends Script {
  val l1 = LogicalAxiom( hof"A" )
  val r1 = LogicalAxiom( hof"A" )
  val p = OrLeftRule( l1, r1, hof"A | A" )
  println( p )

  val nd = LKToND( p )
  println( nd )
}

object orLeft3 extends Script {
  val l1 = LogicalAxiom( hof"A" )
  val r1 = LogicalAxiom( hof"B" )
  val r2 = WeakeningRightRule( r1, hof"C" )
  val r3 = WeakeningLeftRule( r2, hof"D" )
  val p = OrLeftRule( l1, r3, hof"A | D" )
  println( p )

  val nd = LKToND( p )
  println( nd )
}

object orLeft4 extends Script {
  val l1 = LogicalAxiom( hof"A" )
  val l2 = WeakeningRightRule( l1, hof"C" )
  val r1 = LogicalAxiom( hof"B" )
  val r2 = WeakeningRightRule( r1, hof"C" )
  val r3 = WeakeningLeftRule( r2, hof"D" )
  val p = OrLeftRule( l2, r3, hof"A | D" )
  println( p )

  val nd = LKToND( p, Suc( 3 ) )
  println( nd )
}

object orLeft5 extends Script {
  val l1 = LogicalAxiom( hof"A" )
  val l2 = WeakeningLeftRule( l1, hof"A" )
  val l3 = NegRightRule( l2, hof"A" )
  val r1 = LogicalAxiom( hof"B" )
  val r2 = WeakeningRightRule( r1, hof"B" )
  val p = OrLeftRule( l3, r2, hof"A | B" )
  println( p )

  val nd = LKToND( p, Suc( 2 ) )
  println( nd )
}

object impRight1 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = WeakeningRightRule( p1, hof"B" )
  val p3 = ImpRightRule( p2, hof"A -> B" )
  println( p3 )

  val nd = LKToND( p3, Suc( 1 ) )
  println( nd )
}

object impRight2 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = WeakeningRightRule( p1, hof"B" )
  val p3 = ImpRightRule( p2, hof"A -> B" )
  println( p3 )

  val nd = LKToND( p3, Suc( 0 ) )
  println( nd )
}

object orRight1 extends Script {
  val r1 = LogicalAxiom( hof"A" )
  val r2 = WeakeningRightRule( r1, hof"B" )
  val p = OrRightRule( r2, hof"A | B" )
  println( p )

  val nd = LKToND( p )
  println( nd )
}

object orRight2 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = WeakeningLeftRule( p1, hof"B" )
  val p3 = NegRightRule( p2, hof"B" )
  val p = OrRightRule( p3, hof"A | -B" )
  println( p )

  val nd = LKToND( p )
  println( nd )
}

object negLeftRight1 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = NegLeftRule( p1, hof"A" )
  val p = NegRightRule( p2, hof"-A" )

  println( p )

  val nd = LKToND( p )
  println( nd )
}

object negRight1 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = WeakeningLeftRule( p1, hof"B" )
  val p = NegRightRule( p2, hof"B" )

  println( p )

  val nd = LKToND( p )
  println( nd )
}

object weakenContractRight1 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = WeakeningRightRule( p1, hof"A" )
  val p = ContractionRightRule( p2, hof"A" )

  println( p )

  val nd = LKToND( p )
  println( nd )
}

object cut1 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = LogicalAxiom( hof"A" )
  val p = CutRule( p1, Suc( 0 ), p2, Ant( 0 ) )

  println( p )

  val nd = LKToND( p )
  println( nd )
}

object cut2 extends Script {
  val l1 = LogicalAxiom( hof"A" )
  val l2 = WeakeningLeftRule( l1, hof"B" )
  val r1 = LogicalAxiom( hof"A" )
  val r2 = WeakeningRightRule( r1, hof"C" )
  val p = CutRule( l2, Suc( 0 ), r2, Ant( 0 ) )

  println( p )

  val nd = LKToND( p )
  println( nd )
}

object impLeft1 extends Script {
  val l1 = LogicalAxiom( hof"A" )
  val l2 = WeakeningRightRule( l1, hof"C" )
  val r1 = LogicalAxiom( hof"B" )
  val r2 = WeakeningLeftRule( r1, hof"D" )
  val p = ImpLeftRule( l2, r2, hof"A -> B" )

  println( p )

  val nd = LKToND( p )
  //val nd = LKToND( p, Suc( 1 ) )
  println( nd )
}

object impLeft2 extends Script {
  val l1 = LogicalAxiom( hof"A" )
  val r1 = LogicalAxiom( hof"B" )
  val r2 = NegLeftRule( r1, hof"B" )
  val p = ImpLeftRule( l1, r2, hof"A -> B" )

  println( p )

  val nd = LKToND( p )
  //val nd = LKToND( p, Suc( 1 ) )
  println( nd )
}

object lem extends Script {
  val s1 = LogicalAxiom( hof"A" )
  val s2 = NegRightRule( s1, hof"A" )
  val s3 = OrRightRule( s2, hof"A | -A" )

  println( s3 )
  val nd = LKToND( s3 )
  println( nd )
}

object weakeningRight1 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = WeakeningRightRule( p1, hof"A" )
  val p3 = WeakeningRightRule( p2, hof"B" )

  println( p3 )

  val nd = LKToND( p3, Suc( 0 ) )
  println( nd )
}

object weakeningRight2 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = WeakeningRightRule( p1, hof"A" )
  val p3 = WeakeningRightRule( p2, hof"B" )

  println( p3 )

  val nd = LKToND( p3, Suc( 2 ) )
  println( nd )
}

object example1 extends Script {
  val lk = ProofBuilder.
    c( LogicalAxiom( hof"A" ) ).
    u( WeakeningRightRule( _, hof"B" ) ).
    u( WeakeningRightRule( _, hof"C" ) ).
    u( WeakeningRightRule( _, hof"D" ) ).
    u( OrRightRule( _, hof"A | B" ) ).
    u( NegLeftRule( _, hof"A | B" ) ).
    u( OrRightRule( _, hof"C | D" ) ).
    qed
  println( lk )

  val focus = Suc( 0 )
  val nd = LKToND( lk, focus )
  println( nd )
}

object negLeftFollowedByNegRight extends Script {
  val lk = ProofBuilder.
    c( LogicalAxiom( hof"A" ) ).
    u( NegLeftRule( _, hof"A" ) ).
    u( NegRightRule( _, hof"-A" ) ).
    qed

  val focus = Suc( 0 )
  val nd = LKToND( lk, focus )

  println( lk )
  println( nd )
}

object contractRightWithWrongFocus extends Script {
  val lk = ProofBuilder.
    c( LogicalAxiom( hof"B" ) ).
    u( WeakeningRightRule( _, hof"B" ) ).
    u( WeakeningRightRule( _, hof"C" ) ).
    u( ContractionRightRule( _, hof"B" ) ).
    qed

  val focus = Suc( 0 )
  val nd = LKToND( lk, focus )

  println( lk )
  println( nd )
}

object weakeningRightWithWrongFocus extends Script {
  val lk = ProofBuilder.
    c( LogicalAxiom( hof"B" ) ).
    u( WeakeningRightRule( _, hof"A" ) ).
    qed

  val focus = Suc( 0 )
  println( s"focus: ${lk.endSequent( focus )}" )
  val nd = LKToND( lk, focus )

  println( lk )
  println( nd )
}

object equalityLeft extends Script {
  val c = FOLConst( "c" )
  val d = FOLConst( "d" )
  val Pc = FOLAtom( "P", c )
  val Pd = FOLAtom( "P", d )

  val lk = ProofBuilder.
    c( LogicalAxiom( Pc ) ).
    u( WeakeningLeftRule( _, Pd ) ).
    u( WeakeningRightRule( _, Pd ) ).
    u( WeakeningLeftRule( _, hof"$c = $d" ) ).
    u( EqualityLeftRule( _, Eq( c, d ), Pc, Pd ) ).
    qed

  val focus = Suc( 0 )
  val nd = LKToND( lk, focus )

  println( lk )
  println( nd )
}

object equalityRight extends Script {
  val c = FOLConst( "c" )
  val d = FOLConst( "d" )
  val Pc = FOLAtom( "P", c )
  val Pd = FOLAtom( "P", d )

  val lk = ProofBuilder.
    c( LogicalAxiom( Pc ) ).
    u( WeakeningLeftRule( _, Pd ) ).
    u( WeakeningRightRule( _, Pd ) ).
    u( WeakeningLeftRule( _, hof"$c = $d" ) ).
    u( EqualityRightRule( _, Eq( c, d ), Pc, Pd ) ).
    qed

  val focus = Suc( 0 )
  val nd = LKToND( lk, focus )

  println( lk )
  println( nd )
}