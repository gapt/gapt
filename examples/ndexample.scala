package examples

import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.proofs.nd._

object ndexample extends Script {
  val a1 = LogicalAxiom( hof"a" )
  val a2 = LogicalAxiom( hof"b" )
  val a3 = AndIntroRule(a1, a2, hof"a & b")

  val a4 = AndElim1Rule(a3)
  println(a4)

  val a5 = AndElim2Rule(a3)
  println(a5)

  val a6 = AndIntroRule(a4, a5)
  println(a6)
}

object ndImpElimExample extends Script {
  val a1 = LogicalAxiom( hof"a" )
  val a2 = LogicalAxiom( Imp( hof"a",hof"b" )  )
  val a3 = ImpElimRule(a2,a1)
  println(a3)
}