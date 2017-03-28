package at.logic.gapt.proofs.nd

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable._

class NDTest extends Specification with SatMatchers {

  "doubleNegationElim" in {
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

    val a5 = OrElimRule( c5, b1, a4 )
    val a6 = ImpIntroRule( a5 )

    a6.conclusion must beValidSequent
  }

  "Example 1" in {
    val a1 = LogicalAxiom( hof"p" )
    val a2 = AndIntroRule( a1, a1 )
    val a3 = ContractionRule( a2, hof"p" )
    val a4 = ImpIntroRule( a3 )

    a4.conclusion must beValidSequent
  }

  "Weakening" in {
    val a1 = LogicalAxiom( hof"a" )
    val a2 = WeakeningRule( a1, hof"b" )

    a2.conclusion must beValidSequent
  }

  "LogicalAxiom" in {
    val a1 = LogicalAxiom( hof"a", Seq( hof"b", hof"c" ) )

    a1.conclusion must beValidSequent
  }

  "And" in {
    val a1 = LogicalAxiom( hof"a" )
    val a2 = LogicalAxiom( hof"b" )
    val a3 = AndIntroRule( a1, a2 )

    val a4 = AndElim1Rule( a3 )

    val a5 = AndElim2Rule( a3 )

    val a6 = AndIntroRule( a4, a5 )

    val a7 = ContractionRule( a6, hof"a" )
    val a8 = ContractionRule( a7, hof"b" )

    a8.conclusion must beValidSequent
  }

  "Forall" in {
    val a1 = LogicalAxiom( hof"!x P x" )
    val a2 = ForallElimRule( a1, hov"v" )

    val a3 = ForallIntroRule( a2, hof"!y P y", hov"v" )
    val a4 = ImpIntroRule( a3 )

    val b1 = LogicalAxiom( hof"!y P y" )
    val b2 = ForallElimRule( b1, hov"v" )
    val b3 = ForallIntroRule( b2, hof"!x P x", hov"v" )
    val b4 = ImpIntroRule( b3 )

    val res = AndIntroRule( a4, b4 )

    res.conclusion mustEqual Sequent() :+ hof"(!x P x -> !y P y) & (!y P y -> !x P x)"
  }

  "Induction" in {
    val b1 = LogicalAxiom( hof"!(x: nat) (((x + (0: nat)): nat) = x)" )
    val b2 = ForallElimRule( b1, hof"((((x:nat) + (0: nat)): nat) = x)", le"0: nat", hov"x: nat" )

    val s1 = LogicalAxiom( hof"!(x: nat) !(y: nat) (((s(x): nat) + y: nat) = s(x + y))" )
    val s2 = ForallElimRule( s1, hof"!(y: nat) (((s(x0): nat) + y: nat) = s(x0 + y))", le"x0: nat", hov"x: nat" )
    val s3 = ForallElimRule( s2, hof"((((s(x0): nat) + (0: nat)): nat) = s(x0 + 0))", le"0: nat", hov"y: nat" )
    val s4 = LogicalAxiom( hof"(((x0: nat) + (0: nat)): nat) = x0" )
    val s5 = EqualityElimRule( s4, s3, hof"((((s(x0): nat) + (0: nat)): nat) = s(z: nat))", hov"z: nat" )

    s5.conclusion( Suc( 0 ) ) mustEqual hof"(((s(x0:nat): nat) + (0:nat)): nat) = s(x0)"

    val cases = Seq(
      InductionCase( b2, hoc"0: nat", Seq.empty, Seq.empty ),
      InductionCase( s5, hoc"s: nat>nat", Seq( Ant( 0 ) ), Seq( hov"x0: nat" ) )
    )
    val p = InductionRule( cases, Abs( Var( "x", TBase( "nat" ) ), hof"(((x: nat) + (0:nat)): nat) = x" ), le"x: nat" )

    p.conclusion mustEqual Seq( hof"!(x: nat) ((x + (0:nat)): nat) = x", hof"!(x: nat) !(y: nat) (((s(x): nat) + y): nat) = s(x + y)" ) ++: Sequent() :+ hof"(((x: nat) + (0: nat)): nat) = x"
  }

  "ImpElim" in {
    val a1 = LogicalAxiom( hof"a" )
    val a2 = LogicalAxiom( hof"a -> b" )
    val a3 = ImpElimRule( a2, a1 )

    a3.conclusion must beValidSequent
  }

  "ImpIntro" in {
    val a1 = LogicalAxiom( hof"a", Seq( hof"b" ) )
    val a2 = ImpIntroRule( a1, Ant( 0 ) )
    val a3 = ImpIntroRule( a2 )

    a3.conclusion must beValidSequent
  }

  "OrElim" in {
    val a1 = LogicalAxiom( hof"a & b" )
    val a2 = AndElim1Rule( a1 )
    val a3 = LogicalAxiom( hof"a & c" )
    val a4 = AndElim1Rule( a3 )
    val a5 = LogicalAxiom( hof"(a & b) | (a & c)" )

    val a6 = OrElimRule( a5, a2, a4 )
    a6.conclusion must beValidSequent
  }

  "OrIntro1" in {
    val a1 = LogicalAxiom( hof"a & b" )
    val a7 = OrIntro1Rule( a1, hof"a" )
    a7.conclusion must beValidSequent
  }

  "OrIntro2" in {
    val a1 = LogicalAxiom( hof"a & b" )
    val a8 = OrIntro2Rule( a1, hof"a" )
    a8.conclusion must beValidSequent
  }

  "BottomElim" in {
    val a1 = LogicalAxiom( Bottom() )
    val a2 = BottomElimRule( a1, hof"a" )

    a2.conclusion must beValidSequent
  }

  "Negation" in {
    val a1 = LogicalAxiom( hof"¬a" )
    val a2 = LogicalAxiom( hof"a" )
    val a3 = NegElimRule( a1, a2 )
    val a4 = NegIntroRule( a3, Ant( 0 ) )

    a4.conclusion must beValidSequent
  }

  "ExistsIntro 1" in {
    val a1 = LogicalAxiom( hof"P a b" )
    val a2 = ExistsIntroRule( a1, hof"P x b", hoc"a : i", hov"x" )

    a2.conclusion mustEqual Seq( hof"P a b" ) ++: Sequent() :+ hof"?x P x b"
  }

  "ExistsIntro 2" in {
    val a1 = LogicalAxiom( hof"P a b" )
    val a3 = ExistsIntroRule( a1, hof"?x P x b", hoc"a : i" )

    a3.conclusion mustEqual Seq( hof"P a b" ) ++: Sequent() :+ hof"?x P x b"
  }

  "ExistsIntro 3" in {
    val a4 = LogicalAxiom( hof"P x b" )
    val a5 = ExistsIntroRule( a4, hof"?x P x b" )
    val a6 = ExistsIntroRule( a5, hof"?y ?x P x y", hoc"b : i" )

    a6.conclusion mustEqual Seq( hof"P x b" ) ++: Sequent() :+ hof"?y ?x P x y"
  }

  "ExistsElim" in {
    val a1 = LogicalAxiom( hof"?x P x" )
    val a2 = LogicalAxiom( hof"!x (P x -> Q)" )
    val a3 = ForallElimRule( a2, hov"y" )
    val a4 = LogicalAxiom( hof"P y" )
    val a5 = ImpElimRule( a3, a4 )
    val a6 = ExistsElimRule( a1, a5, hov"y" )

    a6.conclusion mustEqual Seq( hof"?x P x", hof"!x (P x -> Q)" ) ++: Sequent() :+ hof"Q"
  }

  "ExcludedMiddle" in {
    val a1 = LogicalAxiom( hof"P" )
    val a2 = LogicalAxiom( hof"¬P" )
    val a3 = OrIntro1Rule( a1, hof"¬P" )
    val a4 = OrIntro2Rule( a2, hof"P" )
    val a5 = ExcludedMiddleRule( a3, Ant( 0 ), a4, Ant( 0 ) )

    a5.conclusion must beValidSequent
  }

  "TheoryAxiom" in {
    val a1 = TheoryAxiom( fof"!x x = x" )

    a1.conclusion must beEValidSequent
  }

  "EqualityElim 1" in {
    val a1 = LogicalAxiom( fof"!x0!x1 P(x2)" )
    val a2 = LogicalAxiom( fof"x2=x3" )
    val a3 = EqualityElimRule( a2, a1 )

    a3.conclusion mustEqual Seq( fof"x2 = x3", fof"!x0 !x1 P x2" ) ++: Sequent() :+ fof"!x0 !x1 P x3"
  }

  "EqualityElim 2" in {
    val a1 = LogicalAxiom( fof"!x0!x1 P(x2)" )
    val a2 = LogicalAxiom( fof"x2=x3" )
    val a4 = EqualityElimRule( a2, a1, fof"!x0!x1 P(x2)", fov"x2" )

    a4.conclusion mustEqual Seq( fof"x2 = x3", fof"!x0 !x1 P x2" ) ++: Sequent() :+ fof"!x0 !x1 P x3"
  }

  "EqualityElim 3" in {
    val b1 = LogicalAxiom( fof"!x0!x1 P(x1)" )
    val b2 = LogicalAxiom( fof"x1=x2" )
    val b4 = EqualityElimRule( b2, b1, fof"!x0!x1 P(x1)", fov"x1" )
    b4.conclusion mustEqual Seq( fof"x1 = x2", fof"!x0 !x1 P x1" ) ++: Sequent() :+ fof"!x0 !x1 P x1"
  }

  "EqualityElim 4" in {
    val c1 = LogicalAxiom( fof"!x0!x1 P(x2)" )
    val c2 = LogicalAxiom( fof"x2=x1" )
    val c3 = EqualityElimRule( c2, c1 )
    c3.conclusion mustEqual Seq( fof"x2 = x1", fof"!x0 !x1 P x2" ) ++: Sequent() :+ fof"!x0 !x1_0 P x1"
  }

  "EqualityElim 5" in {
    val c1 = LogicalAxiom( fof"!x0!x1 P(x2)" )
    val c2 = LogicalAxiom( fof"x2=x1" )
    val c4 = EqualityElimRule( c2, c1, fof"!x0!x1 P(x2)", fov"x2" )
    c4.conclusion mustEqual Seq( fof"x2 = x1", fof"!x0 !x1 P x2" ) ++: Sequent() :+ fof"!x0 !x1_0 P x1"
  }

  "EqualityIntro fov" in {
    val a1 = EqualityIntroRule( fov"x" )
    a1.conclusion must beEValidSequent
  }

  "EqualityIntro foc" in {
    val a2 = EqualityIntroRule( foc"c" )
    a2.conclusion must beEValidSequent
  }

}
