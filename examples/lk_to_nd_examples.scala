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

  LKToND( s6 )
}
