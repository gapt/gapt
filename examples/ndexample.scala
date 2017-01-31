package examples

import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.proofs.nd.{AndIntroRule, LogicalAxiom}

object ndexample extends Script {
  val a1 = LogicalAxiom( hof"a" )
  val a2 = LogicalAxiom( hof"b" )
  val a3 = AndIntroRule(a1, a2, hof"a & b")

  println(a3)
}