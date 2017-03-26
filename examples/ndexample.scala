package at.logic.gapt.examples

import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.nd._

object doubleNegationElim extends Script {
  val a1 = LogicalAxiom( hof"¬¬A" )
  val a2 = LogicalAxiom( hof"¬A" )
  val a3 = NegElimRule( a1, a2 )
  val a4 = BottomElimRule( a3, hof"A" )

  val b1 = LogicalAxiom( hof"A" )

  val c1 = LogicalAxiom( hof"A" )
  val c2 = LogicalAxiom( hof"¬A" )
  val c3 = OrIntro1Rule( c1, hof"¬A" )
  val c4 = OrIntro2Rule( c2, hof"A" )
  val c5 = ExcludedMiddleRule( c3, Ant( 0 ), c4, Ant( 0 ) )

  val a5 = OrElimRule( b1, a4, c5 )
  val a6 = ImpIntroRule( a5 )

  println( a6 )
}

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

/*
inductionCase([p4] ∀x ((0:nat) + (x:nat): nat) = x ⊢ 0 + 0 = 0    (ForallLeftRule(p3, Ant(0), ((0:nat) + (x:nat): nat) = x, 0:nat, x:nat))
[p3] ((0:nat) + 0: nat) = 0 ⊢ 0 + 0 = 0    (EqualityRightRule(p2, Ant(0), Suc(0), λx (x:nat) = 0))
[p2] ((0:nat) + 0: nat) = 0 ⊢ 0 = 0    (WeakeningLeftRule(p1, ((0:nat) + 0: nat) = 0))
[p1]  ⊢ (0:nat) = 0    (ReflexivityAxiom(0:nat))
,0:nat,Vector(),List(),Suc(0))
 */
/*
InductionCase([p7] ∀x ∀y ((s(x:nat): nat) + (y:nat): nat) = s(x + y),
x_0 + 0 = x_0
⊢
s(x_0) + 0 = s(x_0)    (ForallLeftRule(p6, Ant(0), ∀y ((s(x:nat): nat) + (y:nat): nat) = s(x + y), x_0:nat, x:nat))
[p6] ∀y ((s(x_0:nat): nat) + (y:nat): nat) = s(x_0 + y),
x_0 + 0 = x_0
⊢
s(x_0) + 0 = s(x_0)    (ForallLeftRule(p5, Ant(0), ((s(x_0:nat): nat) + (y:nat): nat) = s(x_0 + y), 0:nat, y:nat))
[p5] ((s(x_0:nat): nat) + (0:nat): nat) = s(x_0 + 0),
x_0 + 0 = x_0
⊢
s(x_0) + 0 = s(x_0)    (EqualityRightRule(p4, Ant(0), Suc(0), λx (x:nat) = s(x_0:nat)))
[p4] ((s(x_0:nat): nat) + (0:nat): nat) = s(x_0 + 0),
x_0 + 0 = x_0
⊢
s(x_0 + 0) = s(x_0)    (WeakeningLeftRule(p3, ((s(x_0:nat): nat) + (0:nat): nat) = s(x_0 + 0)))
[p3] ((x_0:nat) + (0:nat): nat) = x_0 ⊢ (s(x_0 + 0): nat) = s(x_0)    (EqualityRightRule(p2, Ant(0), Suc(0), λx (s(x:nat): nat) = s(x_0)))
[p2] ((x_0:nat) + (0:nat): nat) = x_0 ⊢ (s(x_0): nat) = s(x_0)    (WeakeningLeftRule(p1, ((x_0:nat) + (0:nat): nat) = x_0))
[p1]  ⊢ (s(x_0:nat): nat) = s(x_0)    (ReflexivityAxiom(s(x_0:nat): nat))
,s:nat>nat,Vector(Ant(1)),List(x_0:nat),Suc(0))
 */
object ndInductionExample extends Script {
  val b1 = LogicalAxiom(hof"!(x: nat) (((x + (0: nat)): nat) = x)")
  val b2 = ForallElimRule(b1, hof"((((x:nat) + (0: nat)): nat) = x)", le"0: nat", hov"x: nat")

  val s1 = LogicalAxiom(hof"!(x: nat) !(y: nat) (((s(x): nat) + y: nat) = s(x + y))")
  val s2 = ForallElimRule(s1, hof"!(y: nat) (((s(x0): nat) + y: nat) = s(x0 + y))", le"x0: nat", hov"x: nat")
  val s3 = ForallElimRule(s2, hof"((((s(x0): nat) + (0: nat)): nat) = s(x0 + 0))", le"0: nat", hov"y: nat")
  val s4 = LogicalAxiom(hof"(((x0: nat) + (0: nat)): nat) = x0")
  val s5 = EqualityElimRule(s4, s3, hof"((((s(x0): nat) + (0: nat)): nat) = s(x0 + 0))", hov"x0: nat")

  // is assert(s5.conclusion(Suc(0)) == hof"(((s(x0:nat): nat) + (0:nat)): nat) = s(x0 + 0)")
  // should be
  assert(s5.conclusion(Suc(0)) == hof"(((s(x0:nat): nat) + (0:nat)): nat) = s(x0)")

  val cases = Seq(
    InductionCase(b2, hoc"0: nat", Seq.empty, Seq.empty),
    InductionCase(s5, hoc"s: nat>nat", Seq(Ant(0)), Seq(hov"x0: nat"))

  )
  val p = InductionRule(cases, Abs(Var("x", TBase("nat")), hof"(((x: nat) + (0:nat)): nat) = x"), le"x: nat")

  println(p)
}

object ndImpElimExample extends Script {
  val a1 = LogicalAxiom( hof"a" )
  val a2 = LogicalAxiom( hof"a -> b" )
  val a3 = ImpElimRule( a2, a1 )
  println( a3 )
}

object ndImpIntroExample extends Script {
  val a1 = LogicalAxiom( hof"a", Seq( hof"b" ) )
  val a2 = ImpIntroRule( a1, Ant( 0 ) )
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
  val a1 = LogicalAxiom( hof"¬a" )
  val a2 = LogicalAxiom( hof"a" )
  val a3 = NegElimRule( a1, a2 )
  val a4 = NegIntroRule( a3, Ant( 0 ) )
  println( a4 )
}

object existsIntroExample extends Script {
  val a1 = LogicalAxiom( hof"P a b" )
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
  val a5 = ExcludedMiddleRule( a3, Ant( 0 ), a4, Ant( 0 ) )
  println( a5 )
}

object theoryAxiom extends Script {
  val a1 = TheoryAxiom( fof"!x x = x" )
  println( a1 )
}

object equalityElim extends Script {
  val a1 = LogicalAxiom( fof"!x0!x1 P(x2)" )
  val a2 = LogicalAxiom( fof"x2=x3" )
  val a3 = EqualityElimRule( a2, a1 )
  println( a3 )
  val a4 = EqualityElimRule( a2, a1, fof"!x0!x1 P(x2)", fov"x2" )
  println( a4 )

  val b1 = LogicalAxiom( fof"!x0!x1 P(x1)" )
  val b2 = LogicalAxiom( fof"x1=x2" )
  val b4 = EqualityElimRule( b2, b1, fof"!x0!x1 P(x1)", fov"x1" )
  println( b4 )
  // val b5 = EqualityElimRule( b2, b1, fof"!x0!x1 P(x3)", fov"x3" )
  // println(b5)
  // val b6 = EqualityElimRule( b2, b1 )
  // println(b6)

  val c1 = LogicalAxiom( fof"!x0!x1 P(x2)" )
  val c2 = LogicalAxiom( fof"x2=x1" )
  val c3 = EqualityElimRule( c2, c1 )
  println( c3 )
  val c4 = EqualityElimRule( c2, c1, fof"!x0!x1 P(x2)", fov"x2" )
  println( c4 )
}

object equalityIntro extends Script {
  val a1 = EqualityIntroRule( fov"x" )
  println( a1 )
  val a2 = EqualityIntroRule( foc"c" )
  println( a2 )
}