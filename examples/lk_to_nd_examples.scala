package at.logic.examples.nd
import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lk._

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

  val nd = LKToND( s10, Some( Suc( 0 ) ) )
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

  val nd = LKToND( s6, Some( Suc( 0 ) ) )
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

  val nd = LKToND( p2, Some( Suc( 0 ) ) )
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

  val nd = LKToND( p5, Some( Suc( 0 ) ) )
  println( nd )
}

object orLeft1 extends Script {
  val l1 = LogicalAxiom( hof"A" )
  val r1 = LogicalAxiom( hof"B" )
  val p = OrLeftRule( l1, r1, hof"A | B" )
  println( p )

  val nd = LKToND( p, Some( Suc( 0 ) ) )
  println( nd )
}

object orLeft2 extends Script {
  val l1 = LogicalAxiom( hof"A" )
  val r1 = LogicalAxiom( hof"A" )
  val p = OrLeftRule( l1, r1, hof"A | A" )
  println( p )

  val nd = LKToND( p, Some( Suc( 0 ) ) )
  println( nd )
}

object orLeft3 extends Script {
  val l1 = LogicalAxiom( hof"A" )
  val r1 = LogicalAxiom( hof"B" )
  val r2 = WeakeningRightRule( r1, hof"C" )
  val r3 = WeakeningLeftRule( r2, hof"D" )
  val p = OrLeftRule( l1, r3, hof"A | D" )
  println( p )

  val nd = LKToND( p, Some( Suc( 0 ) ) )
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

  val nd = LKToND( p, Some( Suc( 3 ) ) )
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

  val nd = LKToND( p, Some( Suc( 2 ) ) )
  println( nd )
}

object impRight1 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = WeakeningRightRule( p1, hof"B" )
  val p3 = ImpRightRule( p2, hof"A -> B" )
  println( p3 )

  val nd = LKToND( p3, Some( Suc( 1 ) ) )
  println( nd )
}

object impRight2 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = WeakeningRightRule( p1, hof"B" )
  val p3 = ImpRightRule( p2, hof"A -> B" )
  println( p3 )

  val nd = LKToND( p3, Some( Suc( 0 ) ) )
  println( nd )
}

object orRight1 extends Script {
  val r1 = LogicalAxiom( hof"A" )
  val r2 = WeakeningRightRule( r1, hof"B" )
  val p = OrRightRule( r2, hof"A | B" )
  println( p )

  val nd = LKToND( p, Some( Suc( 0 ) ) )
  println( nd )
}

object orRight2 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = WeakeningLeftRule( p1, hof"B" )
  val p3 = NegRightRule( p2, hof"B" )
  val p = OrRightRule( p3, hof"A | -B" )
  println( p )

  val nd = LKToND( p, Some( Suc( 0 ) ) )
  println( nd )
}

object negLeftRight1 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = NegLeftRule( p1, hof"A" )
  val p = NegRightRule( p2, hof"-A" )

  println( p )

  val nd = LKToND( p, Some( Suc( 0 ) ) )
  println( nd )
}

object negRight1 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = WeakeningLeftRule( p1, hof"B" )
  val p = NegRightRule( p2, hof"B" )

  println( p )

  val nd = LKToND( p, Some( Suc( 0 ) ) )
  println( nd )
}

object weakenContractRight1 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = WeakeningRightRule( p1, hof"A" )
  val p = ContractionRightRule( p2, hof"A" )

  println( p )

  val nd = LKToND( p, Some( Suc( 0 ) ) )
  println( nd )
}

object cut1 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = LogicalAxiom( hof"A" )
  val p = CutRule( p1, Suc( 0 ), p2, Ant( 0 ) )

  println( p )

  val nd = LKToND( p, Some( Suc( 0 ) ) )
  println( nd )
}

object cut2 extends Script {
  val l1 = LogicalAxiom( hof"A" )
  val l2 = WeakeningLeftRule( l1, hof"B" )
  val r1 = LogicalAxiom( hof"A" )
  val r2 = WeakeningRightRule( r1, hof"C" )
  val p = CutRule( l2, Suc( 0 ), r2, Ant( 0 ) )

  println( p )

  val nd = LKToND( p, Some( Suc( 0 ) ) )
  println( nd )
}

object impLeft1 extends Script {
  val l1 = LogicalAxiom( hof"A" )
  val l2 = WeakeningRightRule( l1, hof"C" )
  val r1 = LogicalAxiom( hof"B" )
  val r2 = WeakeningLeftRule( r1, hof"D" )
  val p = ImpLeftRule( l2, r2, hof"A -> B" )

  println( p )

  val nd = LKToND( p, Some( Suc( 0 ) ) )
  //val nd = LKToND( p, Some( Suc( 1 ) )
  println( nd )
}

object impLeft2 extends Script {
  val l1 = LogicalAxiom( hof"A" )
  val r1 = LogicalAxiom( hof"B" )
  val r2 = NegLeftRule( r1, hof"B" )
  val p = ImpLeftRule( l1, r2, hof"A -> B" )

  println( p )

  val nd = LKToND( p, None )
  //val nd = LKToND( p, Some( Suc( 1 ) ) )
  println( nd )
}

object lem extends Script {
  val s1 = LogicalAxiom( hof"A" )
  val s2 = NegRightRule( s1, hof"A" )
  val s3 = OrRightRule( s2, hof"A | -A" )

  println( s3 )
  val nd = LKToND( s3, Some( Suc( 0 ) ) )
  println( nd )
}

object weakeningRight1 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = WeakeningRightRule( p1, hof"A" )
  val p3 = WeakeningRightRule( p2, hof"B" )

  println( p3 )

  val nd = LKToND( p3, Some( Suc( 0 ) ) )
  println( nd )
}

object weakeningRight2 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = WeakeningRightRule( p1, hof"A" )
  val p3 = WeakeningRightRule( p2, hof"B" )

  println( p3 )

  val nd = LKToND( p3, Some( Suc( 2 ) ) )
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
  val nd = LKToND( lk, Some( focus ) )
  println( nd )
}

object negLeftFollowedByNegRight extends Script {
  val lk = ProofBuilder.
    c( LogicalAxiom( hof"A" ) ).
    u( NegLeftRule( _, hof"A" ) ).
    u( NegRightRule( _, hof"-A" ) ).
    qed

  val focus = Suc( 0 )
  val nd = LKToND( lk, Some( focus ) )

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
  val nd = LKToND( lk, Some( focus ) )

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
  val nd = LKToND( lk, Some( focus ) )

  println( lk )
  println( nd )
}

object equalityLeft extends Script {
  val c = FOLConst( "c" )
  val d = FOLConst( "d" )
  val Pc = FOLAtom( "P", c )
  val Pd = FOLAtom( "P", d )
  val Pccc = FOLAtom( "P", c, c, c )
  val Pccd = FOLAtom( "P", c, c, d )

  val lk = ProofBuilder.
    c( LogicalAxiom( Pc ) ).
    u( WeakeningLeftRule( _, Pccc ) ).
    u( WeakeningLeftRule( _, Pd ) ).
    u( WeakeningRightRule( _, Pd ) ).
    u( WeakeningLeftRule( _, hof"$c = $d" ) ).
    u( EqualityLeftRule( _, Eq( c, d ), Pccc, Pccd ) ).
    qed

  val focus = Suc( 0 )
  val nd = LKToND( lk, Some( focus ) )

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
  val nd = LKToND( lk, Some( focus ) )

  println( lk )
  println( nd )
}

object induction extends Script {
  val x = FOLVar( "x" )
  val y = FOLVar( "y" )
  val zero = FOLConst( "0" )
  val Sx = FOLFunction( "s", List( x ) )

  val P0y = FOLAtom( "P", List( zero, y ) )
  val Pxy = FOLAtom( "P", List( x, y ) )
  val PSxy = FOLAtom( "P", List( Sx, y ) )

  val ax1 = LogicalAxiom( P0y )

  val ax2 = ProofLink( foc"th", hos"$Pxy :- $PSxy" )

  val lk = InductionRule(
    Seq(
      InductionCase( ax1, FOLConst( "0" ), Seq(), Seq(), Suc( 0 ) ),
      InductionCase( ax2, FOLFunctionConst( "s", 1 ), Seq( Ant( 0 ) ), Seq( x ), Suc( 0 ) ) ),
    Abs( x, Pxy ), x )

  val focus = Suc( 0 )
  val nd = LKToND( lk, Some( focus ) )

  println( lk )
  println( nd )
}

object equalityLeftEmptySuc extends Script {
  val c = FOLConst( "c" )
  val d = FOLConst( "d" )
  val Pc = FOLAtom( "P", c )
  val Pd = FOLAtom( "P", d )

  val lk = ProofBuilder.
    c( LogicalAxiom( Pc ) ).
    u( NegLeftRule( _, Suc( 0 ) ) ).
    u( WeakeningLeftRule( _, Pd ) ).
    u( WeakeningLeftRule( _, hof"$c = $d" ) ).
    u( EqualityLeftRule( _, Eq( c, d ), Pc, Pd ) ).
    qed

  val focus = Suc( 0 )
  val nd = LKToND( lk, Some( focus ) )

  println( lk )
  println( nd )
}

object weakeningRight extends Script {
  val lk = WeakeningRightRule( BottomAxiom, hof"p" )

  val focus = Suc( 0 )
  val nd = LKToND( lk, Some( focus ) )

  println( lk )
  println( nd )
}

object negLeft extends Script {
  val lk = WeakeningRightRule( NegLeftRule( LogicalAxiom( hof"q" ), Suc( 0 ) ), hof"p" )

  val focus = Suc( 0 )
  val nd = LKToND( lk, Some( focus ) )

  println( lk )

  println( nd )
}

object proofLink extends Script {
  implicit var ctx = Context.default
  ctx += Context.Sort( "i" )
  ctx += hoc"'<': i>i>o"
  ctx += hoc"'+': i>i>i"
  ctx += hoc"'1': i"
  ctx += hoc"'3': i"
  ctx += hoc"'ax': i>i>i"
  ctx += ( "ax", hos"x + 1 < y :- x < y" )
  val lk = ProofLink( le"ax 1 3", hos"1 + 1 < 3 :- 1 < 3" )
  ctx.check( lk )

  val focus = Some( Suc( 0 ) )
  val nd = LKToND( lk, focus )

  println( lk )
  println( nd )
}

object proofLink2 extends Script {
  implicit var ctx = Context.default
  ctx += Context.Sort( "i" )
  ctx += hoc"'<': i>i>o"
  ctx += hoc"'1': i"
  ctx += hoc"'2': i"
  ctx += hoc"'3': i"
  ctx += hoc"'ax': i>i>i>i"
  ctx += ( "ax", hos"x < y, y < z :- x < z" )
  val lk = ProofLink( le"ax 1 2 3", hos"1 < 2, 2 < 3 :- 1 < 3" )
  ctx.check( lk )

  val focus = Some( Suc( 0 ) )
  val nd = LKToND( lk, focus )

  println( lk )
  println( nd )
}

object proofLink3 extends Script {
  implicit var ctx = Context.default
  ctx += Context.Sort( "i" )
  ctx += hoc"'<': i>i>o"
  ctx += hoc"'1': i"
  ctx += hoc"'2': i"
  ctx += hoc"'3': i"
  ctx += hoc"'ax': i>i>i>i>i"
  ctx += ( "ax", hos"x < y, y < z :- x < z, x < a, a < a" )
  val lk = ProofLink( le"ax 1 1 2 3", hos"1 < 2, 2 < 3 :- 1 < 3, 1 < 1, 1 < 1" )
  ctx.check( lk )

  val focus = Some( Suc( 0 ) )
  val nd = LKToND( lk, focus )

  println( lk )
  println( nd )
}

object AndLeftWithEmptySuccedent extends Script {
  val lk = ProofBuilder.
    c( LogicalAxiom( hof"A" ) ).
    u( NegLeftRule( _, hof"A" ) ).
    u( AndLeftRule( _, hof"A & -A" ) ).
    qed

  val focus = None
  val nd = LKToND( lk, focus )

  println( lk )
  println( nd )
}

object OrLeftWithEmptySuccedent extends Script {
  val lk = ProofBuilder.
    c( LogicalAxiom( hof"A" ) ).
    u( NegLeftRule( _, hof"A" ) ).
    c( LogicalAxiom( hof"B" ) ).
    u( NegLeftRule( _, hof"B" ) ).
    b( OrLeftRule( _, _, hof"A | B" ) ).
    qed

  val focus = None
  val nd = LKToND( lk, focus )

  println( lk )
  println( nd )
}

object inductionRule extends Script {
  val x = FOLVar( "x" )
  val zero = FOLConst( "0" )
  val Sx = FOLFunction( "s", List( x ) )

  val P0 = FOLAtom( "P", List( zero ) )
  val Px = FOLAtom( "P", List( x ) )
  val PSx = FOLAtom( "P", List( Sx ) )

  val ax1 = LogicalAxiom( P0 )

  implicit var ctx = Context.default
  ctx += Context.InductiveType( "i", hoc"0: i", hoc"s: i>i" )
  ctx += hoc"'th': i>i"
  ctx += hoc"'P': i>o"
  ctx += ( "th", hos"$Px :- $PSx" )

  val ax2 = ProofLink( le"th x", hos"$Px :- $PSx" )

  val lk = InductionRule(
    Seq(
      InductionCase( ax1, hoc"0: i", Seq(), Seq(), Suc( 0 ) ),
      InductionCase( ax2, hoc"s: i>i", Seq( Ant( 0 ) ), Seq( x ), Suc( 0 ) ) ),
    Abs( x, Px ), x )
  ctx.check( lk )

  val focus = Some( Suc( 0 ) )
  val nd = LKToND( lk, focus )

  println( lk )
  println( nd )
}

object definitionLeftRule extends Script {
  val lk = ProofBuilder.
    c( LogicalAxiom( hof"A" ) ).
    u( WeakeningLeftRule( _, hof"B" ) ).
    u( DefinitionLeftRule( _, Ant( 0 ), hof"C" ) ).
    qed

  val focus = Some( Suc( 0 ) )
  val nd = LKToND( lk, focus )

  println( lk )
  println( nd )
}

object definitionRightRule extends Script {
  val lk = ProofBuilder.
    c( LogicalAxiom( hof"A" ) ).
    u( WeakeningRightRule( _, hof"B" ) ).
    u( DefinitionRightRule( _, Suc( 1 ), hof"C" ) ).
    qed

  val focus = Some( Suc( 0 ) )
  val nd = LKToND( lk, focus )

  println( lk )
  println( nd )
}

object definitionRightRule2 extends Script {
  val lk = ProofBuilder.
    c( LogicalAxiom( hof"A" ) ).
    u( WeakeningRightRule( _, hof"B" ) ).
    u( DefinitionRightRule( _, Suc( 1 ), hof"C" ) ).
    qed

  val focus = Some( Suc( 1 ) )
  val nd = LKToND( lk, focus )

  println( lk )
  println( nd )
}

object classicalPairing extends Script {
  val p1 = LogicalAxiom( hof"x" )
  val p2 = LogicalAxiom( hof"y" )
  val p3 = BottomAxiom
  val p4 = ImpLeftRule( p2, Suc( 0 ), p3, Ant( 0 ) )
  val p5 = ImpLeftRule( p1, Suc( 0 ), p4, Ant( 0 ) )
  val p6 = WeakeningRightRule( p5, hof"⊥" )
  val p7 = ImpRightRule( p6, Ant( 0 ), Suc( 0 ) )
  val p8 = ImpRightRule( p7, Ant( 1 ), Suc( 0 ) )
  val p9 = ImpRightRule( p8, Ant( 0 ), Suc( 0 ) )
  val lk = p9

  println( lk )

  val focus = Some( Suc( 0 ) )
  val nd = LKToND( lk, focus )

  println( nd )
}