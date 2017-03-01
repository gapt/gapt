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
  val s4 = NegLeftRule( s3, hof"A | B")
  val s5 = NegRightRule( s4, hof"A" )

  val r1 = LogicalAxiom( hof"B" )
  val r2 = WeakeningRightRule( r1, hof"A" )
  val r3 = OrRightRule( r2, hof"A | B" )
  val r4 = NegLeftRule( r3, hof"A | B")
  val r5 = NegRightRule( r4, hof"B" )

  val p1 = AndRightRule( s5, r5, hof"-A & -B")
  val p2 = ContractionLeftRule( p1, hof"-(A | B)")
  println( p2 )

  val nd = LKToND( p2 )
  println(nd)
}

object demorgan2 extends Script {
  val s1 = LogicalAxiom( hof"A" )
  val s2 = NegLeftRule( s1, hof"A" )
  val s3 = WeakeningLeftRule( s2, hof"B" )
  println( s3 )

  val r1 = LogicalAxiom( hof"B" )
  val r2 = NegLeftRule( r1, hof"B" )
  val r3 = WeakeningLeftRule( r2, hof"A" )
  println( r3 )

  val p1 = OrLeftRule( s3, r3, hof"-A | -B" )
  val p2 = ContractionLeftRule( p1, hof"A" )
  val p3 = ContractionLeftRule( p2, hof"B" )
  val p4 = AndLeftRule( p3, hof"A & B" )
  val p5 = NegRightRule( p4, hof"A & B" )
  println( p5 )

  val nd = LKToND( p5 )
  println(nd)
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
  // TODO: weakening missing
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

object impRight1 extends Script {
  val p1 = LogicalAxiom( hof"A" )
  val p2 = WeakeningRightRule( p1, hof"B" )
  val p3 = ImpRightRule( p2, hof"A -> B" )
  println( p3 )

  val nd = LKToND( p3 )
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

object lem extends Script {
  val s1 = LogicalAxiom( hof"A" )
  val s2 = NegRightRule( s1, hof"A" )
  val s3 = OrRightRule( s2, hof"A | -A" )

  println( s3 )
  val nd = LKToND( s3 )
  println( nd )
}
