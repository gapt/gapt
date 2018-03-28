package at.logic.gapt.examples

import at.logic.gapt.proofs.nd._
import at.logic.gapt.expr.{ Abs, TBase, _ }
import at.logic.gapt.proofs.{ Ant, Checkable, Context, Sequent }
import at.logic.gapt.proofs.Context.{ InductiveType, PrimRecFun }

object divisionByTwo {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "x + 0 = x",
    "x + s(y) = s(x + y)" )
  ctx += PrimRecFun(
    hoc"'*': nat>nat>nat",
    "x * 0 = 0",
    "x * s(y) = (x * y) + x" )

  val mo1 = LogicalAxiom( hof"(x:nat) = (y:nat)" )
  val mo2 = EqualityIntroRule( le"s(x)" )
  val mo3 = EqualityElimRule( mo1, mo2, hof"s(x)=s(z)", hov"z:nat" )
  val mo4 = ImpIntroRule( mo3 )
  val mo5 = ForallIntroRule( mo4, hov"y:nat", hov"y:nat" )
  val mo6 = ForallIntroRule( mo5, hov"x:nat", hov"x:nat" )

  val b1 = EqualityIntroRule( le"0" )
  val b2 = DefinitionRule( b1, hof"0 = s(s(0)) * 0" )
  Checkable.requireDefEq( b1.conclusion.succedent( 0 ), b2.conclusion.succedent( 0 ) )
  val b3 = OrIntro1Rule( b2, hof"0 = (s(s(0)) * 0) + s(0)" )
  val b4 = ExistsIntroRule( b3, hof"0 = s(s(0)) * y | 0 = (s(s(0)) * y) + s(0)", le"0", hov"y:nat" )

  val l1 = LogicalAxiom( hof"x = s(s(0)) * z" )
  val l2 = ForallElimRule( mo6, le"x:nat" )
  val l3 = ForallElimRule( l2, le"s(s(0)) * z" )
  val l4 = DefinitionRule( l3, hof"x = s(s(0)) * z -> s(x) = (s(s(0)) * z) + s(0)" )
  Checkable.requireDefEq( le"s(s(s(0)) * z)", le"(s(s(0)) * z) + s(0)" )
  val l5 = ImpElimRule( l4, l1 )
  val l6 = OrIntro2Rule( l5, hof"s(x) = s(s(0)) * z" )
  val l7 = ExistsIntroRule( l6, hof"s(x) = s(s(0)) * y | s(x) = (s(s(0)) * y) + s(0)", le"z:nat", hov"y:nat" )

  val r1 = LogicalAxiom( hof"x = (s(s(0)) * z) + s(0)" )
  val r2 = ForallElimRule( mo6, le"x:nat" )
  val r3 = ForallElimRule( r2, le"(s(s(0)) * z) + s(0)" )
  val r4 = DefinitionRule( r3, hof"x = (s(s(0)) * z) + s(0) -> s(x) = s(s(0)) * s(z)" )
  Checkable.requireDefEq( le"s(s(s(0)) * z) + s(0)", le"s(s(0)) * s(z)" )
  val r5 = ImpElimRule( r4, r1 )
  val r6 = OrIntro1Rule( r5, hof"s(x) = (s(s(0)) * s(z)) + s(0)" )
  val r7 = ExistsIntroRule( r6, hof"s(x) = s(s(0)) * y | s(x) = (s(s(0)) * y) + s(0)", le"s(z)", hov"y:nat" )

  val i1 = LogicalAxiom( hof"?y (x = s(s(0)) * y | x = (s(s(0)) * y) + s(0))" )
  val i2 = LogicalAxiom( hof"x = s(s(0)) * z | x = (s(s(0)) * z) + s(0)" )
  val i3 = OrElimRule( i2, l7, r7 )
  val i4 = ExistsElimRule( i1, i3, hov"z:nat" )

  val cases = Seq( InductionCase( b4, hoc"0", Seq(), Seq() ), InductionCase( i4, hoc"s", Seq( Ant( 0 ) ), Seq( hov"x:nat" ) ) )
  val a1 = InductionRule( cases, Abs( hov"x:nat", hof"?y (x = s(s(0)) * y | x = (s(s(0)) * y) + s(0))" ), hov"x:nat" )
  val proof = ForallIntroRule( a1, hov"x:nat", hov"x:nat" )
}