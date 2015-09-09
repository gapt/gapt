package at.logic.gapt.proofs.resolutionOld

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.proofs.FOLClause
import at.logic.gapt.proofs.resolutionOld.robinson._
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula
import at.logic.gapt.proofs.resolutionNew.{ findDerivationViaResolution, fixDerivation }
import at.logic.gapt.provers.prover9.Prover9Prover
import org.specs2.mutable._

class FixDerivationTest extends Specification {
  "fixDerivation" should {
    "not say that p :- is derivable from p :- p, r by symmetry" in {
      val p = FOLAtom( "p", Nil )
      val r = FOLAtom( "r", Nil )
      val to = FOLClause( p :: Nil, Nil )
      val from = FOLClause( p :: Nil, p :: r :: Nil )

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
      val from = FOLClause( ab :: bc :: Nil, cd :: Nil )
      val to = FOLClause( cb :: ab :: Nil, dc :: Nil )

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

      val to = FOLClause( pa :: Nil, qx :: Nil )
      val from = FOLClause( px :: py :: Nil, qu :: qv :: Nil )

      fixDerivation.tryDeriveByFactor( to, from ) must beSome
    }

    "obtain a derivation of :- p from { :- q; q :- p } from a derivation of :- p, r from { :- q, r; q :- p }" in {
      val p = FOLAtom( "p" )
      val q = FOLAtom( "q" )
      val r = FOLAtom( "r" )

      val der = Resolution( InitialClause( Nil, q :: r :: Nil ), InitialClause( q :: Nil, p :: Nil ), q, q, FOLSubstitution() )
      val cq = FOLClause( Nil, q :: Nil )
      val cqp = FOLClause( q :: Nil, p :: Nil )

      val cp = FOLClause( Nil, p :: Nil )

      fixDerivation( der, cq :: cqp :: Nil ).root.toHOLSequent must beEqualTo( cp )
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
      val cq = FOLClause( Nil, q :: Nil )
      val cqp = FOLClause( q :: Nil, p :: Nil )

      val cp = FOLClause( Nil, p :: Nil )

      fixDerivation( der, cq :: cqp :: Nil ).root.toHOLSequent must beEqualTo( cp )
    }

  }

  "findDerivationViaResolution" should {
    def isTautological( f: FOLClause ): Boolean =
      ( f.negative intersect f.positive ).nonEmpty ||
        f.positive.collect { case Eq( FOLVar( x ), FOLVar( x_ ) ) if x == x_ => () }.nonEmpty

    def check( a: FOLClause, bs: Set[FOLClause] ) = {
      if ( !new Prover9Prover().isInstalled ) skipped
      findDerivationViaResolution( a, bs ) must beLike {
        case Some( p: RobinsonResolutionProof ) =>
          p.root.toHOLSequent.isSubMultisetOf( a ) aka s"${p.root} subclause of $a" must_== true
          foreach( initialSequents( p ).map( _.toHOLClause ) ) { initial =>
            val inBsModRenaming = bs.exists( b => PCNF.getVariableRenaming( initial, b ).isDefined )
            ( isTautological( initial.map( _.asInstanceOf[FOLAtom] ) ) || inBsModRenaming ) aka s"$initial in $bs or tautology" must_== true
          }
      }
    }

    "-q|p, q := p" in {
      val a = FOLClause( Seq(), Seq( FOLAtom( "p" ) ) )
      val bs = Set( FOLClause( Seq(), Seq( FOLAtom( "q" ) ) ), FOLClause( Seq( FOLAtom( "q" ) ), Seq( FOLAtom( "p" ) ) ) )
      check( a, bs )
    }

    "-p(x)|f(x,y)=y, p(a) := f(a,z)=z" in {
      val a = FOLClause( Seq(), Seq( parseFormula( "f(a,z)=z" ) ) )
      val bs = Set(
        FOLClause( Seq( parseFormula( "p(x)" ) ), Seq( parseFormula( "f(x,y)=y" ) ) ),
        FOLClause( Seq(), Seq( parseFormula( "p(a)" ) ) )
      )
      check( a, bs )
    }

    "p|p|q := p|q" in {
      val a = FOLClause( Seq(), Seq( FOLAtom( "p" ), FOLAtom( "q" ) ) )
      val bs = Set( FOLClause( Seq(), Seq( FOLAtom( "p" ), FOLAtom( "p" ), FOLAtom( "q" ) ) ) )
      check( a, bs )
    }

    "p|q := p|p|q" in {
      val a = FOLClause( Seq(), Seq( FOLAtom( "p" ), FOLAtom( "p" ), FOLAtom( "q" ) ) )
      val bs = Set( FOLClause( Seq(), Seq( FOLAtom( "p" ), FOLAtom( "q" ) ) ) )
      check( a, bs )
    }

    "requires factoring" in {
      val a = FOLClause( Seq( FOLAtom( "p" ) ), Seq() )
      val bs = Set(
        FOLClause( Seq( FOLAtom( "p" ), FOLAtom( "q" ) ), Seq( FOLAtom( "r" ) ) ),
        FOLClause( Seq( FOLAtom( "p" ) ), Seq( FOLAtom( "q" ), FOLAtom( "r" ) ) ),
        FOLClause( Seq( FOLAtom( "p" ), FOLAtom( "r" ) ), Seq() )
      )
      check( a, bs )
    }
  }
}
