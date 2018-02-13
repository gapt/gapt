package at.logic.gapt.examples

import at.logic.gapt.proofs.nd._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Ant, Context, Sequent }
import at.logic.gapt.proofs.Context.{ InductiveType, PrimRecFun }

object addRecorsorsExamples extends Script {

  var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += InductiveType(
    ty"conjj ?c  ?b",
    hoc"pairr{?c ?b}: ?c > ?b > conjj ?c ?b" )
  ctx += InductiveType(
    ty"list ?a",
    hoc"nil{?a}: list ?a",
    hoc"cons{?a}: ?a > list ?a > list ?a" )
  ctx += InductiveType(
    ty"bitree ?a",
    hoc"leaf{?a}: ?a > bitree ?a",
    hoc"node{?a}: bitree ?a > bitree ?a > bitree ?a" )

  MRealizability.setSystemT( ctx )
  implicit var systemT = MRealizability.systemT
  println( systemT )

  systemT += Definition( Const( "length", ty"list ?a > nat", List( ty"?a" ) ), le"listRec(0,^(z1:?a)^(z2: list ?a)^(z3:nat) s(z3))" )
  systemT += Definition( Const( "mirror", ty"bitree ?a > bitree ?a", List( ty"?a" ) ), le"bitreeRec( (^(x:?a)leaf(x)), (^(z1:bitree ?a)^(z2:bitree ?a)^(z3:bitree ?a)^(z4:bitree ?a) node(z4,z2)) )" )

  val plus = le"natRec(s(s(0)))(^z1 ^z2 (s(z2)))"
  println( normalize( App( plus, le"s(s(0))" ) ) )

  val pluspair = le"conjjRec (^x ^y natRec(x,(^z1 ^z2 (s(z2))),y))"
  println( normalize( App( pluspair, le"pairr(s(0),s(s(0)))" ) ) )

  println( normalize( le"length( cons(nil,cons(nil,cons(nil,nil))) )" ) )

  println( normalize( le"mirror( node( leaf(0) , leaf(s(0)) ) )" ) )

  val sum = le"bitreeRec((^x x),(^t1 ^y1 ^t2 ^y2 (natRec(y1,(^z1 ^z2 (s(z2))),y2))))"
  println( normalize( App( sum, le"node(leaf(0),node(leaf(s(0)),leaf(s(s(0)))))" ) ) )

}

object examplesLogicalAxiom extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  val a1 = LogicalAxiom( hof"P(x)" )
  val m1 = MRealizability.mrealize( a1 )
  print( a1 ); print( m1 ); print( " of type " ); print( m1.ty )

  println(); println()

  val a2 = LogicalAxiom( hof"x = y" )
  val m2 = MRealizability.mrealize( a2 )
  print( a2 ); print( m2 ); print( " of type " ); print( m2.ty )

  println(); println()

  val a3 = LogicalAxiom( hof"(x:nat) = y" )
  val m3 = MRealizability.mrealize( a3 )
  print( a3 ); print( m3 ); print( " of type " ); print( m3.ty )

  println(); println()

  val a4 = LogicalAxiom( hof"x = 0 & y = 0" )
  val m4 = MRealizability.mrealize( a4 )
  print( a4 ); print( m4 ); print( " of type " ); print( m4.ty )

  println(); println()

  val a5 = LogicalAxiom( hof" 0 + 0 = 0" )
  val m5 = MRealizability.mrealize( a5 )
  print( a5 ); print( m5 ); print( " of type " ); print( m5.ty )

  println(); println()

  val a6 = LogicalAxiom( hof"!x ?y x + y = s(x)" )
  val m6 = MRealizability.mrealize( a6 )
  print( a6 ); print( m6 ); print( " of type " ); print( m6.ty )

  println(); println()

  val a7 = EqualityIntroRule( le"s(s(s(0)))" )
  val m7 = MRealizability.mrealize( a7 )
  print( a7 ); print( m7 ); print( " of type " ); print( m7.ty )

  println(); println()

  val a8 = EqualityIntroRule( le"x + s(y + z)" )
  val m8 = MRealizability.mrealize( a8 )
  print( a8 ); print( m8 ); print( " of type " ); print( m8.ty )

}

object examplesEqualityIntroRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  val a1 = EqualityIntroRule( le"s(s(s(0)))" )
  val m1 = MRealizability.mrealize( a1 )
  print( a1 ); print( m1 ); print( " of type " ); print( m1.ty )

  println(); println()

  val a2 = EqualityIntroRule( le"x + s(y + z)" )
  val m2 = MRealizability.mrealize( a2 )
  print( a2 ); print( m2 ); print( " of type: " ); print( m2.ty )

}

object examplesWeakeningRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  val a1 = EqualityIntroRule( le"s(s(y))" )
  val a11 = WeakeningRule( a1, hof"!x x = x + (0 + s(z))" )
  val m1 = MRealizability.mrealize( a11 )
  print( a11 ); print( m1 ); print( " of type " ); print( m1.ty )

  println(); println()

  val a2 = LogicalAxiom( hof"s(x) = s(s(y))" )
  val a22 = WeakeningRule( a2, hof"!x x = x + (0 + s(z))" )
  val m2 = MRealizability.mrealize( a22 )
  print( a22 ); print( m2 ); print( " of type " ); print( m2.ty )

  println(); println()

  val a3 = LogicalAxiom( hof"(x : nat) = y" )
  val m3 = MRealizability.mrealize( a3 )
  print( a3 ); print( m3 ); print( " of type " ); print( m3.ty )

  println(); println()

  val a33 = WeakeningRule( a3, hof"!(x:nat) x = z" )
  val m33 = MRealizability.mrealize( a33 )
  print( a33 ); print( m33 ); print( " of type " ); print( m33.ty )

  println(); println()

  val a333 = WeakeningRule( a33, hof"?(x : nat) x = y" )
  val m333 = MRealizability.mrealize( a333 )
  print( a333 ); print( m333 ); print( " of type " ); print( m333.ty )

}

object exampleContractionRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = LogicalAxiom( hof"x = 0" )
  val m1 = MRealizability.mrealize( a1 )
  print( a1 ); print( m1 ); print( " of type " ); print( m1.ty )

  println(); println()

  val a2 = WeakeningRule( a1, hof"(x:nat) = z" )
  val m2 = MRealizability.mrealize( a2 )
  print( a2 ); print( m2 ); print( " of type " ); print( m2.ty )

  println(); println()

  val a3 = WeakeningRule( a2, hof"(x:nat) = y" )
  val m3 = MRealizability.mrealize( a3 )
  print( a3 ); print( m3 ); print( " of type " ); print( m3.ty )

  println(); println()

  val a4 = WeakeningRule( a3, hof"(x:nat) = y" )
  val m4 = MRealizability.mrealize( a4 )
  print( a4 ); print( m4 ); print( " of type " ); print( m4.ty )

  println(); println()

  val a5 = ContractionRule( a4, hof"(x:nat) = y" )
  val m5 = MRealizability.mrealize( a5 )
  print( a5 ); print( m5 ); print( " of type " ); print( m5.ty )

}

object examplesConjuctionRules extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = LogicalAxiom( hof"0 = 0 & s(0) = s(0)" )
  val a2 = AndElim1Rule( a1 )
  val m1 = MRealizability.mrealize( a2 )
  print( a2 ); print( m1 ); print( " of type " ); print( m1.ty )

  println(); println()

  val a11 = LogicalAxiom( hof"x = 0 & y = 0" )
  val a22 = AndElim2Rule( a11 )
  val m11 = MRealizability.mrealize( a22 )
  print( a22 ); print( m11 ); print( " of type " ); print( m11.ty )

  println(); println()

  val a111 = LogicalAxiom( hof"x = 0" )
  val a222 = LogicalAxiom( hof"s(0) = s(0)" )
  val a3 = AndIntroRule( a111, a222 )
  val a4 = AndElim1Rule( a3 )
  val m111 = MRealizability.mrealize( a4 )
  print( a4 ); print( m111 ); print( " of type " ); print( m111.ty )

  println(); println()

  val a1111 = LogicalAxiom( hof"x = 0" )
  val a2222 = LogicalAxiom( hof"s(0) = s(0)" )
  val a33 = AndIntroRule( a1111, a2222 )
  val a44 = AndElim2Rule( a33 )
  val m1111 = MRealizability.mrealize( a44 )
  print( a44 ); print( m1111 ); print( " of type " ); print( m1111.ty )

}

object examplesImplicationRules extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = LogicalAxiom( hof"s(0) = s(0) -> 0 = 0" )
  val a2 = LogicalAxiom( hof"s(0) = s(0)" )
  val a3 = ImpElimRule( a1, a2 )
  val m1 = MRealizability.mrealize( a3 )
  print( a3 ); print( m1 ); print( " of type" ); println( m1.ty )

  println(); println()

  val a11 = LogicalAxiom( hof"0 = 0" )
  val a22 = WeakeningRule( a11, hof"s(0) = s(0)" )
  val a33 = ImpIntroRule( a22, Ant( 0 ) )
  val m22 = MRealizability.mrealize( a33 )
  print( a33 ); print( m22 ); print( " of type " ); println( m22.ty )

}

object examplesForallIntroRules extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  val a1 = EqualityIntroRule( le"x + s(y)" )
  val a2 = ForallIntroRule( a1, hov"x:nat", hov"z:nat" )
  val m1 = MRealizability.mrealize( a2 )
  print( a2 ); print( m1 ); print( " of type " ); print( m1.ty )

  println(); println()

  val a3 = ForallIntroRule( a2, hov"y:nat", hov"y:nat" )
  val m2 = MRealizability.mrealize( a3 )
  print( a3 ); print( m2 ); print( " of type " ); print( m2.ty )

}

object exampleExistsElimRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = LogicalAxiom( hof"?x (x = 0)" )
  val a2 = EqualityIntroRule( le"0" )
  val a3 = WeakeningRule( a2, hof"y = 0" )
  val a4 = ExistsElimRule( a1, a3, hov"y:nat" )
  val m1 = MRealizability.mrealize( a4 )
  print( a4 ); print( m1 ); print( " of type " ); println( m1.ty )

}

object examplesEqualityElimRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  val a1 = LogicalAxiom( hof"!(x0:nat) !(x1:nat) s(x2) = x2 + s(0)" )
  val a2 = LogicalAxiom( hof"(x2:nat) = x3" )
  val a3 = EqualityElimRule( a2, a1 )
  val m1 = MRealizability.mrealize( a3 )
  print( a3 ); print( m1 ); print( " of type " ); print( m1.ty )

  println(); println()

  val b1 = LogicalAxiom( hof"s(x) = x + s(0)" )
  val b2 = LogicalAxiom( hof"!z s(x) = z" )
  val b3 = EqualityElimRule( b1, b2 )
  val b4 = LogicalAxiom( hof"s(0) = 0 + s(0)" )
  val b5 = EqualityElimRule( b4, b3 )
  val m2 = MRealizability.mrealize( b5 )
  print( b5 ); print( m2 ); print( " of type " ); print( m2.ty )

}

object exampleForallElimRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = LogicalAxiom( hof"!x ?y x = s(y)" )
  val a2 = ForallElimRule( a1, le"s(s(0))" )
  val m1 = MRealizability.mrealize( a2 )
  print( a2 ); print( m1 ); print( " of type " ); print( m1.ty )

}

object exampleExistsIntroRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = EqualityIntroRule( le"s(s(x))" )
  val a2 = ExistsIntroRule( a1, hof"y = s(s(x))", le"s(s(x))", hov"y:nat" )
  val m1 = MRealizability.mrealize( a2 )
  print( a2 ); print( m1 ); print( " of type " ); print( m1.ty )

}

object exampleBotElimRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = LogicalAxiom( hof"⊥" )
  val a2 = WeakeningRule( a1, hof"!x ?y y = s(x)" )
  val a3 = BottomElimRule( a2, hof"!x ?y x = s(y)" )
  val m1 = MRealizability.mrealize( a3 )
  print( a3 ); print( m1 ); print( " of type " ); print( m1.ty )

}

object examplesInductionRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  val s0 = LogicalAxiom( hof"!x x + 0 = x" )
  val s01 = ForallElimRule( s0, le"0" )
  val s1 = LogicalAxiom( hof"!x !y s(x) + y = s(x + y)" )
  val s2 = ForallElimRule( s1, le"x0: nat" )
  val s3 = ForallElimRule( s2, le"0" )
  val s4 = LogicalAxiom( hof"x0 + 0 = x0" )
  val s5 = EqualityElimRule( s4, s3, hof"s(x0) + 0 = s(z)", hov"z: nat" )
  val cases = Seq(
    InductionCase( s01, hoc"0", Seq.empty, Seq.empty ),
    InductionCase( s5, hoc"s", Seq( Ant( 0 ) ), Seq( hov"x0: nat" ) ) )
  val p = InductionRule( cases, Abs( Var( "x", TBase( "nat" ) ), hof"x + 0 = x" ), le"x : nat" )
  val m1 = MRealizability.mrealize( p )
  print( p ); print( m1 ); print( " of type " ); print( m1.ty )

  println(); println()

  val a1 = LogicalAxiom( hof"P(0)" )
  val b1 = LogicalAxiom( hof"!x (P(x) -> P(s(x)))" )
  val b2 = ForallElimRule( b1, le"x:nat" )
  val b3 = LogicalAxiom( hof"P(x:nat)" )
  val b4 = ImpElimRule( b2, b3 )
  val casess = Seq(
    InductionCase( a1, hoc"0", Seq(), Seq() ),
    InductionCase( b4, hoc"s", Seq( Ant( 1 ) ), Seq( hov"x:nat" ) ) )
  val c3 = InductionRule( casess, Abs( hov"x:nat", hof"P(x:nat)" ), le"x:nat" )
  val d1 = ForallIntroRule( c3, hov"x:nat", hov"x:nat" )
  val d2 = ImpIntroRule( d1, Ant( 0 ) )
  val d3 = ImpIntroRule( d2 )
  val m2 = MRealizability.mrealize( d3 )
  print( d3 ); print( m2 ); print( " of type " ); print( m2.ty )

}

object exampleTopIntroRule extends Script {

  implicit var ctx = Context()

  val a1 = TopIntroRule()
  val m1 = MRealizability.mrealize( a1 )
  print( a1 ); print( m1 ); print( " of type " ); print( m1.ty )

}

object examplesNegationRules extends Script {

  implicit var ctx = Context()

  val a1 = LogicalAxiom( hof"¬a" )
  val a2 = LogicalAxiom( hof"a" )
  val a3 = NegElimRule( a1, a2 )
  val m1 = MRealizability.mrealize( a3 )
  print( a3 ); print( m1 ); print( " of type " ); print( m1.ty )

  println(); println()

  val a4 = NegIntroRule( a3, Ant( 0 ) )
  val m2 = MRealizability.mrealize( a4 )
  print( a4 ); print( m2 ); print( " of type " ); print( m2.ty )

}

object examplesOrIntroRules extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = EqualityIntroRule( le"0" )
  val a2 = OrIntro1Rule( a1, hof"s(0) = 0" )
  val m1 = MRealizability.mrealize( a2 )
  print( a2 ); print( m1 ); print( " of type " ); print( m1.ty )

  println(); println()

  val a3 = OrIntro2Rule( a1, hof"s(0) = 0" )
  val m2 = MRealizability.mrealize( a3 )
  print( a3 ); print( m2 ); print( " of type " ); print( m2.ty )

}

object exampleOrElimRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val b1 = LogicalAxiom( hof"x = 0 & x = s(0)" )
  val b2 = AndElim1Rule( b1 )
  val b3 = LogicalAxiom( hof"x = 0 & x = s(s(0))" )
  val b4 = AndElim1Rule( b3 )
  val b5 = LogicalAxiom( hof"(x = 0 & x = s(0)) | (x = 0 & x = s(s(0)))" )
  val b6 = OrElimRule( b5, b2, b4 )
  val m1 = MRealizability.mrealize( b6 )
  print( b6 ); print( m1 ); print( " of type " ); print( m1.ty )

}

object examplesTheoryAxiom extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  //val a1 = TheoryAxiom( hof"!y (y+0 = 0)" )
  val a1 = TheoryAxiom( hof"y + 0 = 0" )
  val m1 = MRealizability.mrealize( a1 )
  print( a1 ); print( m1 ); print( " of type " ); print( m1.ty )

  println(); println()

  //val a2 = TheoryAxiom( hof"!z ¬(s(z) = 0)" )
  val a2 = TheoryAxiom( hof"¬ s(z) = 0" )
  val m2 = MRealizability.mrealize( a2 )
  print( a2 ); print( m2 ); print( " of type " ); print( m2.ty )

}
