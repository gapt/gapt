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

object demorgan extends Script {
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

  val nd = LKToND(p2)
  println(nd)
}