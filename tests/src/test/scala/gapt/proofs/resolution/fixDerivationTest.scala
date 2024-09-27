package gapt.proofs.resolution

import gapt.expr._
import gapt.expr.formula.Eq
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLAtomConst
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLVar
import gapt.expr.subst.Substitution
import gapt.logic.clauseSubsumption
import gapt.proofs._
import gapt.provers.escargot.{Escargot, NonSplittingEscargot}
import org.specs2.mutable._

class FixDerivationTest extends Specification with SequentMatchers {
  "fixDerivation" should {
    "not say that p :- is derivable from p :- p, r by symmetry" in {
      val p = FOLAtom("p", Nil)
      val r = FOLAtom("r", Nil)
      val to = HOLClause(p :: Nil, Nil)
      val from = HOLClause(p :: Nil, p :: r :: Nil)

      fixDerivation.tryDeriveBySubsumptionModEq(to, from) must beNone
    }

    "say that a=b, b=c :- c=d is derivable from c=b, a=b :- d=c" in {
      val a = FOLConst("a")
      val b = FOLConst("b")
      val c = FOLConst("c")
      val d = FOLConst("d")
      val ab = Eq(a, b)
      val bc = Eq(b, c)
      val cd = Eq(c, d)
      val cb = Eq(c, b)
      val dc = Eq(d, c)
      val from = HOLClause(ab :: bc :: Nil, cd :: Nil)
      val to = HOLClause(cb :: ab :: Nil, dc :: Nil)

      fixDerivation.tryDeriveBySubsumptionModEq(to, from) must beSome
    }

    "modEqSymm" in {
      clauseSubsumption.modEqSymm(hos":- x=y, p(x,y)", hos":- a=b, p(b,a)") must beSome
      clauseSubsumption.modEqSymm(hos":- x=y, p(x,y)", hos":- a=b, p(a,b)") must beSome
      clauseSubsumption.modEqSymm(hos":- x=y, p(x,y), p(y,x)", hos":- a=b, p(a,b)") must beNone
    }

    "derive modulo subsumption and equation reorientation" in {
      val from = hcl"f(x) = g(y) :- g(y) = h(z)"
      val to = hcl"g(z) = f(y) :- h(x) = g(z)"

      fixDerivation.tryDeriveBySubsumptionModEq(to, from) must beLike {
        case Some(p) => p.conclusion must beMultiSetEqual(to)
      }
    }

    "say that p(a) :- q(x) can be derived by factoring from p(x), p(y) :- q(u), q(v)" in {
      val a = FOLConst("a")
      val x = FOLVar("x")
      val y = FOLVar("y")
      val u = FOLVar("u")
      val v = FOLVar("v")
      val pa = FOLAtom("p", a :: Nil)
      val px = FOLAtom("p", x :: Nil)
      val py = FOLAtom("p", y :: Nil)
      val qx = FOLAtom("q", x :: Nil)
      val qu = FOLAtom("q", u :: Nil)
      val qv = FOLAtom("q", v :: Nil)

      val to = HOLClause(pa :: Nil, qx :: Nil)
      val from = HOLClause(px :: py :: Nil, qu :: qv :: Nil)

      fixDerivation.tryDeriveBySubsumptionModEq(to, from) must beSome
    }

    "obtain a derivation of :- p from { :- q; q :- p } from a derivation of :- p, r from { :- q, r; q :- p }" in {
      val p = FOLAtom("p")
      val q = FOLAtom("q")
      val r = FOLAtom("r")

      val der = Resolution(Input(Clause() :+ q :+ r), Suc(0), Input(q +: Clause() :+ p), Ant(0))
      val cq = HOLClause(Nil, q :: Nil)
      val cqp = HOLClause(q :: Nil, p :: Nil)

      val cp = HOLClause(Nil, p :: Nil)

      fixDerivation(der, cq :: cqp :: Nil).conclusion must beEqualTo(cp)
    }

    "obtain a derivation of :- p from { :- q; q :- p } from a derivation of :- p, r from { :- q, r; q :- p, p }" in {
      val p = FOLAtom("p")
      val q = FOLAtom("q")
      val r = FOLAtom("r")

      val der = Resolution(
        Input(Clause() :+ q :+ r),
        Suc(0),
        Factor(
          Input(q +: Clause() :+ p :+ p),
          Suc(0),
          Suc(1)
        ),
        Ant(0)
      )
      val cq = HOLClause(Nil, q :: Nil)
      val cqp = HOLClause(q :: Nil, p :: Nil)

      val cp = HOLClause(Nil, p :: Nil)

      fixDerivation(der, cq :: cqp :: Nil).conclusion must beEqualTo(cp)
    }

  }

  "mapInputs" should {
    "factor reordered clauses" in {
      val Seq(x, y) = Seq("x", "y") map { FOLVar(_) }
      val c = FOLConst("c")
      val p = FOLAtomConst("p", 1)

      val p1 = Input(Clause() :+ p(x) :+ p(y))
      val p2 = Input(p(c) +: Clause())
      val p3 = Subst(p1, Substitution(x -> c, y -> c))
      val p4 = Factor(p3, Suc(0), Suc(1))
      val p5 = Resolution(p4, Suc(0), p2, Ant(0))

      mapInputClauses(p5) {
        case Sequent(ant, suc) => Input(Clause(ant.reverse, suc.reverse))
      }.conclusion must_== Clause()
    }
  }

  "findDerivationViaResolution" should {
    def check(a: HOLClause, bs: Set[_ <: HOLClause]) = {
      findDerivationViaResolution(a, bs, prover = NonSplittingEscargot) must beLike {
        case Some(p) =>
          p.conclusion.isSubMultisetOf(a) aka s"${p.conclusion} subclause of $a" must_== true
          val inputClauses = p.subProofs.collect { case Input(seq) => seq }
          foreach(inputClauses) { inputClause =>
            bs.toSet[HOLSequent] must contain(inputClause)
          }
      }
    }

    "-q|p, q := p" in {
      val a = HOLClause(Seq(), Seq(FOLAtom("p")))
      val bs = Set(HOLClause(Seq(), Seq(FOLAtom("q"))), HOLClause(Seq(FOLAtom("q")), Seq(FOLAtom("p"))))
      check(a, bs)
    }

    "-p(x)|f(x,y)=y, p(a) := f(a,z)=z" in {
      val a = Clause() :+ hoa"f(a,z)=z"
      val bs = Set(
        hoa"p(x)" +: Clause() :+ hoa"f(x,y)=y",
        Clause() :+ hoa"p(a)"
      )
      check(a, bs)
    }

    "p|p|q := p|q" in {
      val a = HOLClause(Seq(), Seq(FOLAtom("p"), FOLAtom("q")))
      val bs = Set(HOLClause(Seq(), Seq(FOLAtom("p"), FOLAtom("p"), FOLAtom("q"))))
      check(a, bs)
    }

    "p|q := p|p|q" in {
      val a = HOLClause(Seq(), Seq(FOLAtom("p"), FOLAtom("p"), FOLAtom("q")))
      val bs = Set(HOLClause(Seq(), Seq(FOLAtom("p"), FOLAtom("q"))))
      check(a, bs)
    }

    "requires factoring" in {
      val a = HOLClause(Seq(FOLAtom("p")), Seq())
      val bs = Set(
        HOLClause(Seq(FOLAtom("p"), FOLAtom("q")), Seq(FOLAtom("r"))),
        HOLClause(Seq(FOLAtom("p")), Seq(FOLAtom("q"), FOLAtom("r"))),
        HOLClause(Seq(FOLAtom("p"), FOLAtom("r")), Seq())
      )
      check(a, bs)
    }
  }
}
