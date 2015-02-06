package at.logic.algorithms.resolution

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import at.logic.language.lambda.types.To
import at.logic.language.fol.{Equation => FOLEquation, And, Or, Neg, Atom, FOLConst, Imp, FOLVar, Substitution}
import at.logic.proofs.resolution._
import at.logic.proofs.resolution.robinson._
import at.logic.proofs.lk.base.FSequent

@RunWith(classOf[JUnitRunner])
class FixDerivationTest extends SpecificationWithJUnit {
  "fixDerivation" should {
    "not say that p :- is derivable from p :- p, r by symmetry" in {
      val p = Atom( "p", Nil )
      val r = Atom( "r", Nil )
      val to = FClause( p::Nil, Nil )
      val from = FSequent( p::Nil, p::r::Nil )

      fixDerivation.canDeriveBySymmetry( to, from ) must beFalse
    }

    "say that a=b, b=c :- c=d is derivable from c=b, a=b :- d=c" in {
      val a = FOLConst("a")
      val b = FOLConst("b")
      val c = FOLConst("c")
      val d = FOLConst("d")
      val ab = FOLEquation( a, b )
      val bc = FOLEquation( b, c )
      val cd = FOLEquation( c, d )
      val cb = FOLEquation( c, b )
      val dc = FOLEquation( d, c )
      val from = FSequent( ab::bc::Nil, cd::Nil )
      val to = FClause( cb::ab::Nil, dc::Nil )

      fixDerivation.canDeriveBySymmetry( to, from ) must beTrue
    }

    "say that p(a) :- q(x) can be derived by factoring from p(x), p(y) :- q(u), q(v)" in {
      val a = FOLConst("a")
      val x = FOLVar("x")
      val y = FOLVar("y")
      val u = FOLVar("u")
      val v = FOLVar("v")
      val pa = Atom("p", a::Nil)
      val px = Atom("p", x::Nil)
      val py = Atom("p", y::Nil)
      val qx = Atom("q", x::Nil)
      val qu = Atom("q", u::Nil)
      val qv = Atom("q", v::Nil)

      val to = FClause( pa::Nil, qx::Nil )
      val from = FSequent( px::py::Nil, qu::qv::Nil )

      fixDerivation.canDeriveByFactor( to, from ) must beTrue
    }

    "obtain a derivation of :- p from { :- q; q :- p } from a derivation of :- p, r from { :- q, r; q :- p }" in {
      val p = Atom("p")
      val q = Atom("q")
      val r = Atom("r")

      val der = Resolution(InitialClause(Nil, q::r::Nil), InitialClause(q::Nil, p::Nil), q, q, Substitution())
      val cq = FSequent(Nil, q::Nil)
      val cqp = FSequent(q::Nil, p::Nil)

      val cp = FSequent(Nil, p::Nil)

      fixDerivation( der, cq::cqp::Nil ).root.toFSequent must beEqualTo(cp)
    }

    "obtain a derivation of :- p from { :- q; q :- p } from a derivation of :- p, r from { :- q, r; q :- p, p }" in {
      val p = Atom("p")
      val q = Atom("q")
      val r = Atom("r")

      val der = Resolution(InitialClause(Nil, q::r::Nil), 
        Factor(
          InitialClause(q::Nil, p::p::Nil),
        p, 2, true, Substitution()),
      q, q, Substitution())
      val cq = FSequent(Nil, q::Nil)
      val cqp = FSequent(q::Nil, p::Nil)

      val cp = FSequent(Nil, p::Nil)

      fixDerivation( der, cq::cqp::Nil ).root.toFSequent must beEqualTo(cp)
    }

  }
}
