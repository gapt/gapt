package at.logic.gapt.examples

import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.nd._
import at.logic.gapt.prooftool.prooftool

object ndexample extends Script {
  val a1 = LogicalAxiom( hof"a" )
  val a2 = LogicalAxiom( hof"b" )
  val a3 = AndIntroRule( a1, a2 )

  val a4 = AndElim1Rule( a3 )
  println( a4 )

  val a5 = AndElim2Rule( a3 )
  println( a5 )

  val a6 = AndIntroRule( a4, a5 )
  println( a6 )
  prooftool.apply( a6 )
}

object ndImpElimExample extends Script {
  val a1 = LogicalAxiom( hof"a" )
  val a2 = LogicalAxiom( hof"a -> b" )
  val a3 = ImpElimRule( a2, a1 )
  println( a3 )
}

object ndImpIntroExample extends Script {
  val a1 = LogicalAxiom ( hof"a" )
  val a2 = ImpIntroRule ( a1 )
  println(a2)
  prooftool.apply(a2)
}

object ndOrExample extends Script {
  val a1 = LogicalAxiom( hof"a & b" )
  val a2 = AndElim1Rule( a1 )
  val a3 = LogicalAxiom( hof"a & c" )
  val a4 = AndElim1Rule( a3 )
  val a5 = LogicalAxiom( hof"(a & b) | (a & c)" )

  val a6 = OrElimRule( a2, a4, a5 )
  println(a6)

  val a7 = OrIntro1Rule(a1, hof"a")
  println(a7)
  val a8 = OrIntro2Rule(a1, hof"a")
  println(a8)
}