package examples

import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.proofs.nd._
import at.logic.gapt.prooftool.prooftool

object ndexample extends Script {
  val a1 = LogicalAxiom( Seq(), hof"a" )
  val a2 = LogicalAxiom( Seq(), hof"b" )
  val a3 = AndIntroRule(a1, a2)

  val a4 = AndElim1Rule(a3)
  println(a4)

  val a5 = AndElim2Rule(a3)
  println(a5)

  val a6 = AndIntroRule(a4, a5)
  println(a6)
  //prooftool.apply(a6)
}

object ndImpElimExample extends Script {
  val a1 = LogicalAxiom( Seq(), hof"a" )
  val a2 = LogicalAxiom( Seq(), hof"a -> b" )
  val a3 = ImpElimRule(a2,a1)
  println(a3)
}

object ndImpIntroExample extends Script {
  val a1 = LogicalAxiom ( Seq(), hof"a" )
  val a2 = ImpIntroRule ( a1 )
  println(a2)
}