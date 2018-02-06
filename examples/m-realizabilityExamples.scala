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
    ty"conj ?c  ?b",
    hoc"pair{?c ?b}: ?c > ?b > conj ?c ?b" )
  ctx += InductiveType(
    ty"list ?a",
    hoc"nil{?a}: list ?a",
    hoc"cons{?a}: ?a > list ?a > list ?a" )
  ctx += InductiveType(
    ty"bitree ?a",
    hoc"leaf{?a}: ?a > bitree ?a",
    hoc"node{?a}: bitree ?a > bitree ?a > bitree ?a" )

  implicit var ctxx = MRealizability.addRecursors( ctx )

  println( ctxx )

  ctxx += Definition( Const( "length", ty"list ?a > nat", List( ty"?a" ) ), le"listRec(0,^(z1:?a)^(z2: list ?a)^(z3:nat) s(z3))" )
  ctxx += Definition( Const( "mirror", ty"bitree ?a > bitree ?a", List( ty"?a" ) ), le"bitreeRec( (^(x:?a)leaf(x)), (^(z1:bitree ?a)^(z2:bitree ?a)^(z3:bitree ?a)^(z4:bitree ?a) node(z4,z2)) )" )

  val plus = le"natRec(s(s(0)))(^z1 ^z2 (s(z2)))"
  println( normalize( App( plus, le"s(s(0))" ) ) )

  val pluspair = le"conjRec (^x ^y natRec(x,(^z1 ^z2 (s(z2))),y))"
  println( normalize( App( pluspair, le"pair(s(0),s(s(0)))" ) ) )

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
  print( a1 ); print( m1 ); print( " of type: " ); println( m1.ty ); println()

  val a2 = LogicalAxiom( hof"x=y" )
  val m2 = MRealizability.mrealize( a2 )
  print( a2 ); print( m2 ); print( " of type: " ); println( m2.ty ); println()

  val a3 = LogicalAxiom( hof"(x:nat) = y" )
  val m3 = MRealizability.mrealize( a3 )
  print( a3 ); print( m3 ); print( " of type: " ); println( m3.ty ); println()

  val a4 = LogicalAxiom( hof"x = 0 & y = 0" )
  val m4 = MRealizability.mrealize( a4 )
  print( a4 ); print( m4 ); print( " of type: " ); println( m4.ty ); println()

  val a5 = LogicalAxiom( hof" 0 + 0 = 0" )
  val m5 = MRealizability.mrealize( a5 )
  print( a5 ); print( m5 ); print( " of type: " ); println( m5.ty ); println()

  val a6 = LogicalAxiom( hof"!x ?y ( x + y = s(x) )" )
  val m6 = MRealizability.mrealize( a6 )
  print( a6 ); print( m6 ); print( " of type: " ); println( m6.ty ); println()

  val a7 = EqualityIntroRule( le"s(s(s(0)))" )
  val m7 = MRealizability.mrealize( a7 )
  print( a7 ); print( m7 ); print( " of type: " ); println( m7.ty ); println()

  val a8 = EqualityIntroRule( le"x + s(y + z)" )
  val m8 = MRealizability.mrealize( a8 )
  print( a8 ); print( m8 ); print( " of type: " ); println( m8.ty ); println()
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
  print( a1 ); print( m1 ); print( " of type: " ); println( m1.ty ); println()

  val a2 = EqualityIntroRule( le"x + s(y + z)" )
  val m2 = MRealizability.mrealize( a2 )
  print( a2 ); print( m2 ); print( " of type: " ); println( m2.ty ); println()
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
  val a11 = WeakeningRule( a1, hof"!x( x = x + (0 + s(z)))" )
  val m1 = MRealizability.mrealize( a11 )
  print( a11 ); print( m1 ); print( " of type: " ); println( m1.ty ); println()

  val a2 = LogicalAxiom( hof"s(x) = s(s(y))" )
  val a22 = WeakeningRule( a2, hof"!x( x = x + (0 + s(z)))" )
  val m2 = MRealizability.mrealize( a22 )
  print( a22 ); print( m2 ); print( " of type: " ); println( m2.ty ); println()

  val a3 = LogicalAxiom( hof"(x : nat) = y" )
  val a33 = WeakeningRule( a3, hof"!(x:nat)( x = z)" )
  val a333 = WeakeningRule( a33, hof"?(x : nat)(x = y)" )
  val m3 = MRealizability.mrealize( a3 )
  print( a3 ); print( m3 ); print( " of type " ); println( m3.ty ); println()
  val m33 = MRealizability.mrealize( a33 )
  print( a33 ); print( m33 ); print( " of type " ); println( m33.ty ); println()
  val m333 = MRealizability.mrealize( a333 )
  print( a333 ); print( m333 ); print( " of type " ); println( m333.ty ); println()
}

object exampleContraction extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  val a1 = LogicalAxiom( hof"x = 0" )
  val a2 = WeakeningRule( a1, hof"(x:nat) = z" )
  val a3 = WeakeningRule( a2, hof"(x:nat) = y" )
  val a4 = WeakeningRule( a3, hof"(x:nat) = y" )
  val a5 = ContractionRule( a4, hof"(x:nat)=y" )
  val m1 = MRealizability.mrealize( a1 )
  print( a1 ); print( m1 ); print( " of type " ); println( m1.ty ); println()
  val m2 = MRealizability.mrealize( a2 )
  print( a2 ); print( m2 ); print( " of type " ); println( m2.ty ); println()
  val m3 = MRealizability.mrealize( a3 )
  print( a3 ); print( m3 ); print( " of type " ); println( m3.ty ); println()
  val m4 = MRealizability.mrealize( a4 )
  print( a4 ); print( m4 ); print( " of type " ); println( m4.ty ); println()
  val m5 = MRealizability.mrealize( a5 )
  print( a5 ); print( m5 ); print( " of type " ); println( m5.ty ); println()
}

object examplesConjuction extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  val a1 = LogicalAxiom( hof"0 = 0 & s(0) = s(0)" )
  val a2 = AndElim1Rule( a1 )
  val m1 = MRealizability.mrealize( a2 )
  print( a2 ); print( m1 ); print( " of type: " ); println( m1.ty ); println()

  val a11 = LogicalAxiom( hof"x = 0 & y = 0" )
  val a22 = AndElim2Rule( a11 )
  val m11 = MRealizability.mrealize( a22 )
  print( a22 ); print( m11 ); print( " of type: " ); println( m11.ty ); println()

  val a111 = LogicalAxiom( hof"x = 0" )
  val a222 = LogicalAxiom( hof"s(0) = s(0)" )
  val a3 = AndIntroRule( a111, a222 )
  val a4 = AndElim1Rule( a3 )
  val m111 = MRealizability.mrealize( a4 )
  print( a4 ); print( m111 ); print( " of type: " ); println( m111.ty ); println()

  val a1111 = LogicalAxiom( hof"x = 0" )
  val a2222 = LogicalAxiom( hof"s(0) = s(0)" )
  val a33 = AndIntroRule( a1111, a2222 )
  val a44 = AndElim2Rule( a33 )
  val m1111 = MRealizability.mrealize( a44 )
  print( a44 ); print( m1111 ); print( " of type: " ); println( m1111.ty ); println()
}

object examplesImplication extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  val a1 = LogicalAxiom( hof"s(0) = s(0) -> 0 =0" )
  val a2 = LogicalAxiom( hof"s(0) = s(0)" )
  val a3 = ImpElimRule( a1, a2 )
  val m1 = MRealizability.mrealize( a3 )
  print( a3 ); print( m1 ); print( " of type" ); println( m1.ty ); println()

  val a11 = LogicalAxiom( hof"0 = 0" )
  val a22 = WeakeningRule( a11, hof"s(0) = s(0)" )
  val a33 = ImpIntroRule( a22, Ant( 0 ) )
  val m22 = MRealizability.mrealize( a33 )
  print( a33 ); print( m22 ); print( " of type " ); println( m22.ty ); println()
}

object exampleForallIntro extends Script {

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
  val a2 = ForallIntroRule( a1, Var( "x", ty"nat" ), Var( "z", ty"nat" ) )
  val a3 = ForallIntroRule( a2, Var( "y", ty"nat" ), Var( "y", ty"nat" ) )
  val m1 = MRealizability.mrealize( a2 )
  print( a2 ); print( m1 ); print( " of type " ); println( m1.ty ); println()

}

object exampleExistsElim extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  val a1 = LogicalAxiom( hof"?(x:nat) (x = 0)" )
  val a2 = EqualityIntroRule( le"0" )
  val a3 = WeakeningRule( a2, hof"y = 0" )
  val a4 = ExistsElimRule( a1, a3, Var( "y", ty"nat" ) )
  val m1 = MRealizability.mrealize( a4 )
  print( a4 ); print( m1 ); print( " of type " ); println( m1.ty ); println()
}

object exampleEqualityElimRule extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  val a1 = LogicalAxiom( hof"!(x0:nat)!(x1:nat) (s(x2)=x2+s(0))" )
  val a2 = LogicalAxiom( hof"(x2:nat)=x3" )
  val a3 = EqualityElimRule( a2, a1 )
  val m1 = MRealizability.mrealize( a3 )
  print( a3 ); print( m1 ); print( " of type " ); println( m1.ty ); println()

}

/*
object theoryAxiom1 extends Script {
  val a1 = TheoryAxiom( hof"!z (s(z) = 0 -> ⊥)" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type: " ); println( m1.ty )
}

object theoryAxiom2 extends Script {
  val a1 = TheoryAxiom( hof"!y (y*0 = 0)" )
  val m1 = MRealizability.mrealize( a1 )
  print( m1 ); print( " of type: " ); println( m1.ty )
}
*/ 