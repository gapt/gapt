package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.proofs.lk.base.FSequent
import at.logic.gapt.proofs.resolution.robinson._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula
import at.logic.gapt.provers.prover9.Prover9Prover
import org.specs2.mutable._

class FixDerivationTest extends Specification {
  "fixDerivation" should {
    "not say that p :- is derivable from p :- p, r by symmetry" in {
      val p = FOLAtom( "p", Nil )
      val r = FOLAtom( "r", Nil )
      val to = FClause( p :: Nil, Nil )
      val from = FSequent( p :: Nil, p :: r :: Nil )

      fixDerivation.tryDeriveBySymmetry( to, from ) must beNone
    }

    "say that a=b, b=c :- c=d is derivable from c=b, a=b :- d=c" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val c = FOLConst( "c" )
      val d = FOLConst( "d" )
      val ab = Eq( a, b )
      val bc = Eq( b, c )
      val cd = Eq( c, d )
      val cb = Eq( c, b )
      val dc = Eq( d, c )
      val from = FSequent( ab :: bc :: Nil, cd :: Nil )
      val to = FClause( cb :: ab :: Nil, dc :: Nil )

      fixDerivation.tryDeriveBySymmetry( to, from ) must beSome
    }

    "say that p(a) :- q(x) can be derived by factoring from p(x), p(y) :- q(u), q(v)" in {
      val a = FOLConst( "a" )
      val x = FOLVar( "x" )
      val y = FOLVar( "y" )
      val u = FOLVar( "u" )
      val v = FOLVar( "v" )
      val pa = FOLAtom( "p", a :: Nil )
      val px = FOLAtom( "p", x :: Nil )
      val py = FOLAtom( "p", y :: Nil )
      val qx = FOLAtom( "q", x :: Nil )
      val qu = FOLAtom( "q", u :: Nil )
      val qv = FOLAtom( "q", v :: Nil )

      val to = FClause( pa :: Nil, qx :: Nil )
      val from = FSequent( px :: py :: Nil, qu :: qv :: Nil )

      fixDerivation.tryDeriveByFactor( to, from ) must beSome
    }

    "obtain a derivation of :- p from { :- q; q :- p } from a derivation of :- p, r from { :- q, r; q :- p }" in {
      val p = FOLAtom( "p" )
      val q = FOLAtom( "q" )
      val r = FOLAtom( "r" )

      val der = Resolution( InitialClause( Nil, q :: r :: Nil ), InitialClause( q :: Nil, p :: Nil ), q, q, FOLSubstitution() )
      val cq = FSequent( Nil, q :: Nil )
      val cqp = FSequent( q :: Nil, p :: Nil )

      val cp = FSequent( Nil, p :: Nil )

      fixDerivation( der, cq :: cqp :: Nil ).root.toFSequent must beEqualTo( cp )
    }

    "obtain a derivation of :- p from { :- q; q :- p } from a derivation of :- p, r from { :- q, r; q :- p, p }" in {
      val p = FOLAtom( "p" )
      val q = FOLAtom( "q" )
      val r = FOLAtom( "r" )

      val der = Resolution(
        InitialClause( Nil, q :: r :: Nil ),
        Factor(
          InitialClause( q :: Nil, p :: p :: Nil ),
          p, 2, true, FOLSubstitution()
        ),
        q, q, FOLSubstitution()
      )
      val cq = FSequent( Nil, q :: Nil )
      val cqp = FSequent( q :: Nil, p :: Nil )

      val cp = FSequent( Nil, p :: Nil )

      fixDerivation( der, cq :: cqp :: Nil ).root.toFSequent must beEqualTo( cp )
    }

  }

  "findDerivationViaResolution" should {
    def isTautological( f: FClause ): Boolean =
      ( f.neg intersect f.pos ).nonEmpty ||
        f.pos.collect { case Eq( FOLVar( x ), FOLVar( x_ ) ) if x == x_ => () }.nonEmpty

    def check( a: FClause, bs: Set[FClause] ) = {
      if ( !new Prover9Prover().isInstalled ) skipped
      findDerivationViaResolution( a, bs ) must beLike {
        case Some( p ) =>
          p.root.toFClause.isSubClauseOf( a ) aka s"${p.root} subclause of $a" must_== true
          foreach( initialSequents( p ).map( _.toFClause ) ) { initial =>
            val inBsModRenaming = bs.exists( b => PCNF.getVariableRenaming( initial, b ).isDefined )
            ( isTautological( initial ) || inBsModRenaming ) aka s"$initial in $bs or tautology" must_== true
          }
      }
    }

    "-q|p, q := p" in {
      val a = FClause( Seq(), Seq( FOLAtom( "p" ) ) )
      val bs = Set( FClause( Seq(), Seq( FOLAtom( "q" ) ) ), FClause( Seq( FOLAtom( "q" ) ), Seq( FOLAtom( "p" ) ) ) )
      check( a, bs )
    }

    "-p(x)|f(x,y)=y, p(a) := f(a,z)=z" in {
      val a = FClause( Seq(), Seq( parseFormula( "f(a,z)=z" ) ) )
      val bs = Set(
        FClause( Seq( parseFormula( "p(x)" ) ), Seq( parseFormula( "f(x,y)=y" ) ) ),
        FClause( Seq(), Seq( parseFormula( "p(a)" ) ) )
      )
      check( a, bs )
    }

    "p|p|q := p|q" in {
      val a = FClause( Seq(), Seq( FOLAtom( "p" ), FOLAtom( "q" ) ) )
      val bs = Set( FClause( Seq(), Seq( FOLAtom( "p" ), FOLAtom( "p" ), FOLAtom( "q" ) ) ) )
      check( a, bs )
    }

    "p|q := p|p|q" in {
      val a = FClause( Seq(), Seq( FOLAtom( "p" ), FOLAtom( "p" ), FOLAtom( "q" ) ) )
      val bs = Set( FClause( Seq(), Seq( FOLAtom( "p" ), FOLAtom( "q" ) ) ) )
      check( a, bs )
    }

    "requires factoring" in {
      val a = FClause( Seq( FOLAtom( "p" ) ), Seq() )
      val bs = Set(
        FClause( Seq( FOLAtom( "p" ), FOLAtom( "q" ) ), Seq( FOLAtom( "r" ) ) ),
        FClause( Seq( FOLAtom( "p" ) ), Seq( FOLAtom( "q" ), FOLAtom( "r" ) ) ),
        FClause( Seq( FOLAtom( "p" ), FOLAtom( "r" ) ), Seq() )
      )
      check( a, bs )
    }
  }
}
