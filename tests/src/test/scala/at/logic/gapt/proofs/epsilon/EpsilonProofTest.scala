package at.logic.gapt.proofs.epsilon

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Context, MutableContext, Sequent }
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class EpsilonProofTest extends Specification with SatMatchers {

  "linear example" in {
    val p = EpsilonProof(
      Seq( le"c", le"f c", le"f (f c)", le"f (f (f c))" ) map {
        CriticalFormula( hof"∃x ¬(P x ⊃ P (f x))", _ )
      },
      hof"P c" +: hof"∀x (P x ⊃ P (f x))" +: Sequent() :+ hof"P (f (f (f (f c))))" )
    p.deep must beValidSequent
  }

  "quantifier blocks" in {
    Escargot getEpsilonProof hof"∀x∀y∀z P(x,y,z) ⊃ ∃x∃y∃z P(f x, g y, h z)" must beLike {
      case Some( p ) =>
        p.deep must beValidSequent
    }
  }

  "deskolemization" in {
    Escargot getEpsilonProof hof"∀x∃y∀z P(x,y,z) ⊃ ∃z∀x∃y P(x,y,z)" must beLike {
      case Some( p ) =>
        p.deep must beValidSequent
    }
  }

  "many sorted 1" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += Context.InductiveType( ty"nat", hoc"0 : nat", hoc"s : nat > nat" )
    ctx += hoc"P: nat > o"
    Escargot.getEpsilonProof( hof"!x (P x -> P (s x)) -> P 0 -> P (s (s 0))" ) must beLike {
      case Some( p ) =>
        p.deep must beValidSequent
    }
  }

  "many sorted 2" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += Context.InductiveType( ty"list ?a", hoc"nil{?a} : list ?a", hoc"cons{?a} : ?a > list ?a > list ?a" )
    ctx += hoc"P{?a}: list ?a > o"
    ctx += Context.Sort( "i" ) // TODO(gabriel): escargot fails when proving the goal with list ?a
    val f = hof"!xs!(x:i) (P xs -> P (cons x xs)) -> P (nil: list i) -> !x P (cons x nil : list i)"
    Escargot.getEpsilonProof( f ) must beLike {
      case Some( p ) =>
        p.deep must beValidSequent
    }
  }

}
