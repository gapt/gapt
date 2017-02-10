package at.logic.gapt.examples

import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.nd._

object ex extends Script {
  val a1 = LogicalAxiom( hof"p" )
  val a2 = AndIntroRule( a1, a1 )
  val a3 = ContractionRule( a2, hof"p" )
  val a4 = ImpIntroRule( a3 )
  println( a4 )
}

object ndWeakeningExample extends Script {
  val a1 = LogicalAxiom( hof"a" )
  val a2 = WeakeningRule( a1, hof"b" )
  println( a2 )
}

object ndLogicalAxiomExample extends Script {
  val a1 = LogicalAxiom( hof"a", Seq( hof"b", hof"c" ) )
  println( a1 )
}

object ndAndExample extends Script {
  val a1 = LogicalAxiom( hof"a" )
  val a2 = LogicalAxiom( hof"b" )
  val a3 = AndIntroRule( a1, a2 )

  val a4 = AndElim1Rule( a3 )

  val a5 = AndElim2Rule( a3 )

  val a6 = AndIntroRule( a4, a5 )

  val a7 = ContractionRule( a6, hof"a" )
  val a8 = ContractionRule( a7, hof"b" )
  println( a8 )
}

object ndForallExample extends Script {
  val a1 = LogicalAxiom( hof"!x P x" )
  val a2 = ForallElimRule( a1, hov"v" )

  //val a3 = ForallIntroRule( a2, hov"v", hov"y" )
  val a3 = ForallIntroRule( a2, hof"!y P y", hov"v" )
  val a4 = ImpIntroRule( a3 )

  val b1 = LogicalAxiom( hof"!y P y" )
  val b2 = ForallElimRule( b1, hov"v" )
  val b3 = ForallIntroRule( b2, hof"!x P x", hov"v" )
  val b4 = ImpIntroRule( b3 )

  val res = AndIntroRule( a4, b4 )

  println( res )
}

object ndInductionExample extends Script {
  val a1 = LogicalAxiom( hof"A 0" )
  val a2 = LogicalAxiom( hof"!x (A x -> A (s x))" )
  val a3 = InductionRule( a1, a2, hoc"t:i" )
  println( a3 )
}

object ndImpElimExample extends Script {
  val a1 = LogicalAxiom( hof"a" )
  val a2 = LogicalAxiom( hof"a -> b" )
  val a3 = ImpElimRule( a2, a1 )
  println( a3 )
}

object ndImpIntroExample extends Script {
  val a1 = LogicalAxiom( hof"a", Seq( hof"b" ) )
  val a2 = ImpIntroRule( a1 , Ant( 0 ) )
  val a3 = ImpIntroRule( a2 )
  println( a3 )
}

object ndOrExample extends Script {
  val a1 = LogicalAxiom( hof"a & b" )
  val a2 = AndElim1Rule( a1 )
  val a3 = LogicalAxiom( hof"a & c" )
  val a4 = AndElim1Rule( a3 )
  val a5 = LogicalAxiom( hof"(a & b) | (a & c)" )

  val a6 = OrElimRule( a2, a4, a5 )
  println( a6 )

  val a7 = OrIntro1Rule( a1, hof"a" )
  println( a7 )
  val a8 = OrIntro2Rule( a1, hof"a" )
  println( a8 )
}

object ndBottomExample extends Script {
  val a1 = LogicalAxiom( Bottom() )
  val a2 = BottomElimRule( a1, hof"a" )
  println( a2 )
}

object negationExample extends Script {
  val a1 = LogicalAxiom( hof"a" )
  val a2 = LogicalAxiom( hof"¬a" )
  val a3 = NegElimRule( a1, a2 )
  val a4 = NegIntroRule( a3, Ant( 0 ) )
  println( a4 )
}

object existsIntroExample extends Script {
  val a1 = LogicalAxiom( hof"P a b")
  val a2 = ExistsIntroRule( a1, hof"P x b", hoc"a : i", hov"x" )
  println( a2 )

  val a3 = ExistsIntroRule( a1, hof"?x P x b", hoc"a : i" )
  println( a3 )

  val a4 = LogicalAxiom( hof"P x b" )
  val a5 = ExistsIntroRule( a4, hof"?x P x b" )
  println( a5 )

  val a6 = ExistsIntroRule( a5, hof"?y ?x P x y", hoc"b : i" )
  println( a6 )
}

object existsElimExample extends Script {
  val a1 = LogicalAxiom( hof"?x P x" )
  val a2 = LogicalAxiom( hof"!x (P x -> Q)" )
  val a3 = ForallElimRule( a2, hov"y" )
  val a4 = LogicalAxiom( hof"P y" )
  val a5 = ImpElimRule( a3, a4 )
  val a6 = ExistsElimRule( a1, a5, hov"y" )
  println( a6 )
}

object lemExample extends Script {
  val a1 = LogicalAxiom( hof"P" )
  val a2 = LogicalAxiom( hof"¬P" )
  val a3 = OrIntro1Rule( a1, hof"¬P" )
  val a4 = OrIntro2Rule( a2, hof"P" )
  val a5 = lawOfExcludedMiddleRule( a3, a4, Ant( 0 ), Ant( 0 ) )
  println( a5 )
}