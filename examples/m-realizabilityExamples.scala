package gapt.examples

import gapt.proofs.nd._
import gapt.expr._
import gapt.formats.babel.{ Notation, Precedence }
import gapt.proofs.{ Ant, Checkable }
import gapt.proofs.Context.{ InductiveType, PrimRecFun }
import gapt.proofs.gaptic.TacticsProof

object successor extends TacticsProof {

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += Notation.Infix( "+", Precedence.plusMinus )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )

  val p1 = EqualityIntroRule( le"s(x)" )
  val p2 = DefinitionRule( p1, hof"s(x) = s(0) + x" )
  Checkable.requireDefEq( p1.conclusion.succedent( 0 ), p2.conclusion.succedent( 0 ) )
  val p3 = ExistsIntroRule( p2, hof"y = s(0) + x", le"s(x)", hov"y:nat" )
  val proof = ForallIntroRule( p3, hov"x:nat", hov"x:nat" )
}

object divisionByTwo extends TacticsProof {

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += Notation.Infix( "+", Precedence.plusMinus )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "x + 0 = x",
    "x + s(y) = s(x + y)" )
  ctx += Notation.Infix( "*", Precedence.timesDiv )
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

object elemAtIndex extends TacticsProof {

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += Notation.Infix( "+", Precedence.plusMinus )
  ctx += PrimRecFun(
    hoc"'+': nat>nat>nat",
    "0 + x = x",
    "s(x) + y = s(x + y)" )( ctx )
  ctx += InductiveType(
    ty"list ?a",
    hoc"nil{?a}: list ?a",
    hoc"cons{?a}: ?a > list ?a > list ?a" )
  ctx += PrimRecFun(
    hoc"app{?a}: list ?a > list ?a > list ?a",
    "app(nil{?a},x) = x",
    "app(cons{?a}(x,y),z) = cons{?a}(x,app(y,z))" )
  ctx += PrimRecFun(
    hoc"length{?a}: list ?a > nat",
    "length(nil{?a}) = 0",
    "length(cons{?a}(x,xs)) = s(length(xs))" )

  // proof for !x ¬ ?n 0 = s(x) + n, i.e. !x ¬ 0 >= s(x)
  val s1 = LogicalAxiom( hof"?n (0 = s(x) + n)" )
  Checkable.requireDefEq( le"s(x + n)", le"s(x) + n" )
  val s11 = DefinitionRule( s1, hof"?n (0 = s(x + n))" )
  val s2 = TheoryAxiom( hof"!x ¬ s(x) = 0" )
  val s3 = ForallElimRule( s2, le"x+n" )
  val s4 = LogicalAxiom( hof"0 = s(x + n)" )
  val s5 = EqualityIntroRule( le"0" )
  val s6 = EqualityElimRule( s4, s5, hof"x = 0", hov"x : nat" )
  val s7 = NegElimRule( s3, s6 )
  val s8 = ExistsElimRule( s11, s7 )
  val s9 = NegIntroRule( s8 )
  val s = ForallIntroRule( s9, hov"x:nat", hov"x:nat" )

  val a1 = LogicalAxiom( hof"xs0 = app(ys,cons(x,zs)) & length(ys) = n0" )
  val a2 = AndElim2Rule( a1 )
  val a3 = EqualityIntroRule( le"s(length(ys))" )
  val a4 = EqualityElimRule( a2, a3, hof"s(length(ys)) = s(x)", hov"x:nat" )
  Checkable.requireDefEq( le"s(length(ys))", le"length(cons(x0,ys))" )
  val a5 = DefinitionRule( a4, hof"length(cons(x0,ys)) = s(n0)" )

  val b1 = LogicalAxiom( hof"xs0 = app(ys,cons(x,zs)) & length(ys) = n0" )
  val b2 = AndElim1Rule( b1 )
  val b3 = EqualityIntroRule( le"cons(x0,xs0)" )
  val b4 = EqualityElimRule( b2, b3, hof"cons(x0,xs0) = cons(x0,x)", hov"x:list ?a" )
  Checkable.requireDefEq( le"cons(x0,app(ys,cons(x,zs)))", le"app(cons(x0,ys),cons(x,zs))" )
  val b5 = DefinitionRule( b4, hof"cons(x0,xs0) = app(cons(x0,ys),cons(x,zs))" )

  val c1 = LogicalAxiom( hof"?zs (xs0 = app(ys,cons(x,zs)) & length(ys) = n0)" )
  val c2 = AndIntroRule( b5, a5 )
  val c3 = ContractionRule( c2, Ant( 0 ), Ant( 1 ) )
  val c4 = ExistsIntroRule( c3, hof"cons(x0,xs0) = app(cons(x0,ys),cons(x,zs)) & length(cons(x0,ys)) = s(n0)", le"zs:list ?a", hov"zs:list ?a" )
  val c5 = ExistsElimRule( c1, c4 )
  val c6 = ExistsIntroRule( c5, hof"?zs (cons(x0,xs0) = app(ys,cons(x,zs)) & length(ys) = s(n0))", le"cons(x0,ys)", hov"ys:list ?a" )

  val x1 = TheoryAxiom( hof"!x !y (s(x)=s(y) -> x=y)" )
  val x2 = ForallElimRule( x1, le"length(xs0)" )
  val x3 = ForallElimRule( x2, le"s(n0)+n" )
  val x4 = LogicalAxiom( hof"length(cons(x0,xs0)) = s(s(n0)) + n" )
  Checkable.requireDefEq( le"s(length(xs0))", le"length(cons(x0,xs0))" )
  val x5 = DefinitionRule( x4, hof"s(length(xs0)) = s(s(n0)) + n" )
  Checkable.requireDefEq( le"s(s(n0)) + n", le"s(s(n0) + n)" )
  val x6 = DefinitionRule( x5, hof"s(length(xs0)) = s(s(n0) + n)" )
  val x = ImpElimRule( x3, x6 )

  val ii1 = LogicalAxiom( hof"?n length(cons(x0,xs0)) = s(s(n0)) + n" )
  val ii2 = ExistsIntroRule( x, hof"?n length(xs0)=s(n0)+n" )
  val ii3 = ExistsElimRule( ii1, ii2 )
  val ii4 = LogicalAxiom( hof"?n length(xs0) = s(n0) + n -> ?ys ?zs (xs0 = app(ys,cons(x,zs)) & length(ys) = n0)" )
  val ii5 = ImpElimRule( ii4, ii3 )
  val ii6 = ExistsElimRule( ii5, c6 )
  val ii7 = ImpIntroRule( ii6, Ant( 1 ) )
  val ii8 = ExistsIntroRule( ii7, hof"?x (?n length(cons(x0,xs0)) = s(s(n0)) + n -> ?ys ?zs ( cons(x0,xs0) = app(ys,cons(x,zs)) & length(ys) = s(n0) ) )" )
  val ii9 = LogicalAxiom( hof"!xs ?x (?n length(xs) = s(n0) + n -> ?ys ?zs ( xs = app(ys,cons(x,zs)) & length(ys) = n0 ) )" )
  val ii10 = ForallElimRule( ii9, le"xs0 : list ?a" )
  val ii11 = ExistsElimRule( ii10, ii8 )
  val ii = WeakeningRule( ii11, hof"?x (?n length(xs0) = s(s(n0)) + n -> ?ys ?zs ( xs0 = app(ys,cons(x,zs)) & length(ys) = s(n0) ) )" )

  val ib1 = LogicalAxiom( hof"?n (0 = s(s(n0)) + n)" )
  val ib2 = ForallElimRule( s, le"s(n0)" )
  val ib3 = NegElimRule( ib2, ib1 )
  val ib4 = BottomElimRule( ib3, hof"?ys ?zs (nil{?a} = app(ys,cons(x,zs)) & length(ys) = s(n0))" )
  val ib5 = ImpIntroRule( ib4 )
  val ib6 = ExistsIntroRule( ib5, hof"?n (0 = s(s(n0)) + n) -> ?ys ?zs (nil = app(ys,cons(x,zs)) & length(ys) = s(n0))", le"x:?a", hov"x:?a" )
  Checkable.requireDefEq( le"length(nil{?a})", le"0" )
  val ib = DefinitionRule( ib6, hof"?x (?n length(nil{?a}) = s(s(n0)) + n -> ?ys ?zs (nil{?a} = app(ys,cons(x,zs)) & length(ys) = s(n0)))" )

  val bi1 = EqualityIntroRule( le"cons(x0,xs0)" )
  val bi2 = EqualityIntroRule( le"0" )
  val bi3 = AndIntroRule( bi1, bi2 )
  val bi4 = ExistsIntroRule( bi3, hof"cons(x0,xs0) = cons(x0,zs) & 0 = 0", le"xs0 : list ?a", hov"zs : list ?a" )
  Checkable.requireDefEq( le"cons(x0,zs)", le"app(nil{?a},cons(x0,zs))" )
  val bi5 = DefinitionRule( bi4, hof"?zs (cons(x0,xs0) = app(nil{?a},cons(x0,zs)) & 0 = 0)" )
  Checkable.requireDefEq( le"0", le"length(nil{?a})" )
  val bi6 = DefinitionRule( bi5, hof"?zs (cons(x0,xs0) = app(nil{?a},cons(x0,zs)) & length(nil{?a}) = 0)" )
  val bi7 = ExistsIntroRule( bi6, hof"?zs (cons(x0,xs0) = app(ys,cons(x0,zs)) & length(ys) = 0)", le"nil{?a}", hov"ys : list ?a" )
  val bi8 = WeakeningRule( bi7, hof"?n length(cons(x0,xs0)) = s(0) + n" )
  val bi9 = ImpIntroRule( bi8 )
  val bi10 = ExistsIntroRule( bi9, hof"?n length(cons(x0,xs0)) = s(0) + n -> ?ys ?zs (cons(x0,xs0) = app(ys,cons(x,zs)) & length(ys) = 0)", le"x0 : ?a", hov"x : ?a" )
  val bi = WeakeningRule( bi10, hof"?x (?n length(xs0) = s(0) + n -> ?ys ?zs (xs0 = app(ys,cons(x,zs)) & length(ys) = 0))" )

  val bb1 = LogicalAxiom( hof"?n 0 = s(0) + n" )
  val bb2 = ForallElimRule( s, le"0" )
  val bb3 = NegElimRule( bb2, bb1 )
  val bb4 = BottomElimRule( bb3, hof"?ys ?zs (nil{?a} = app(ys,cons(x,zs)) & length(ys) = 0)" )
  val bb5 = ImpIntroRule( bb4 )
  val bb6 = ExistsIntroRule( bb5, hof"?n 0 = s(0) + n -> ?ys ?zs (nil{?a} = app(ys,cons(x,zs)) & length(ys) = 0)", le"x : ?a", hov"x : ?a" )
  Checkable.requireDefEq( le"0", le"length(nil{?a})" )
  val bb = DefinitionRule( bb6, hof"?x (?n length(nil{?a}) = s(0) + n -> ?ys ?zs (nil{?a} = app(ys,cons(x,zs)) & length(ys) = 0))" )

  val i1 = InductionRule(
    Seq(
      InductionCase( ib, hoc"nil{?a}", Seq(), Seq() ),
      InductionCase( ii, hoc"cons", Seq( Ant( 0 ) ), Seq( hov"x0 : ?a", hov"xs0 : list ?a" ) ) ),
    Abs( hov"xs : list ?a", hof"?x (?n length(xs) = s(s(n0)) + n -> ?ys ?zs (xs = app(ys,cons(x,zs)) & length(ys) = s(n0)))" ),
    hov"xs : list ?a" )
  val i2 = ForallIntroRule( i1, hov"xs : list ?a", hov"xs : list ?a" )
  val i3 = InductionRule(
    Seq(
      InductionCase( bb, hoc"nil{?a}", Seq(), Seq() ),
      InductionCase( bi, hoc"cons", Seq( Ant( 0 ) ), Seq( hov"x0 : ?a", hov"xs0 : list ?a" ) ) ),
    Abs( hov"xs : list ?a", hof"?x (?n length(xs) = s(0) + n -> ?ys ?zs (xs = app(ys,cons(x,zs)) & length(ys) = 0))" ),
    hov"xs : list ?a" )
  val i4 = ForallIntroRule( i3, hov"xs : list ?a", hov"xs : list ?a" )
  val i5 = InductionRule(
    Seq(
      InductionCase( i4, hoc"0", Seq(), Seq() ),
      InductionCase( i2, hoc"s", Seq( Ant( 0 ) ), Seq( hov"n0:nat" ) ) ),
    Abs( hov"n0 : nat", hof"!xs ?x (?n length(xs) = s(n0) + n -> ?ys ?zs (xs = app(ys,cons(x,zs)) & length(ys) = n0))" ),
    hov"n0 : nat" )
  val proof = ForallIntroRule( i5, hov"n0:nat", hov"n0:nat" )
}