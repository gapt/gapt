package gapt.proofs.resolution

import gapt.examples.CountingEquivalence
import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.Ex
import gapt.expr.formula.FOLAtom
import gapt.expr.formula.FOLAtomConst
import gapt.expr.formula.FOLConst
import gapt.expr.formula.FOLVar
import gapt.expr.formula.fol.thresholds
import gapt.expr.formula.hol.CNFn
import gapt.expr.subst.Substitution
import gapt.expr.ty.Ti
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.{ SkolemFunction => SkolemFun }
import gapt.provers.escargot.Escargot
import gapt.proofs.{ ProofBuilder, _ }
import gapt.proofs.expansion.deskolemizeET
import gapt.utils.SatMatchers
import org.specs2.mutable._

class ResolutionToExpansionProofTest extends Specification with SatMatchers with SequentMatchers {
  "simple proof from prover9" should {
    val es = (
      hof"!z P(c,z)" +:
      hof"!x!y!z (P(x,g(z)) -> P(f(x),z) & R(y))" +:
      hof"!x!z (P(x,z) -> Q(x))" +:
      Sequent()
      :+ hof"?x Q(f(f(x)))" )

    "extract expansion sequent" in {
      val Some( robinson ) = Escargot getResolutionProof es
      val expansion = ResolutionToExpansionProof( robinson )
      expansion.deep must beValidSequent
    }
  }

  "tautological clauses with naive CNF" in {
    val p = FOLAtom( "p" )
    val endSequent = Sequent() :+ ( ( p --> -( -p ) ) & ( -( -p ) --> p ) )
    val cnf = CNFn( endSequent.toDisjunction )
    val Some( robinson ) = Escargot getResolutionProof cnf
    val expansion = ResolutionToExpansionProof( fixDerivation( robinson, endSequent ) )
    expansion.shallow must_== endSequent
    expansion.deep must beValidSequent
  }

  "complicated formula with structural CNF" in {
    val x = FOLVar( "x" )
    val Seq( c, d ) = Seq( "c", "d" ) map { FOLConst( _ ) }
    val as = ( 0 to 12 ) map { i => FOLAtomConst( s"a$i", 1 ) }
    val endSequent = thresholds.atMost.oneOf( as map { a => Ex( x, a( x ) ) } ) +: Sequent() :+ ( as( 0 )( c ) --> -as( 1 )( d ) )

    val Some( ref ) = Escargot getResolutionProof endSequent
    val expansion = ResolutionToExpansionProof( ref )
    expansion.shallow must_== endSequent
    expansion.deep must beValidSequent
  }

  "quantified definitions" in {
    val endSequent = Sequent() :+ CountingEquivalence( 2 )

    val Some( ref ) = Escargot getResolutionProof endSequent
    val expansion = ResolutionToExpansionProof( ref )
    expansion.shallow must_== endSequent
    expansion.deep must beValidSequent
  }

  "duplicate bound variables" in {
    val Seq( p, q ) = Seq( "p", "q" ) map { FOLAtomConst( _, 1 ) }
    val Seq( c, d ) = Seq( "c", "d" ) map { FOLConst( _ ) }
    val x = FOLVar( "x" )

    val endSequent = Sequent() :+ ( ( All( x, p( x ) ) | All( x, q( x ) ) ) --> ( p( c ) | q( d ) ) )

    val Some( ref ) = Escargot getResolutionProof endSequent
    val expansion = ResolutionToExpansionProof( ref )
    expansion.shallow must_== endSequent
    expansion.deep must beValidSequent
  }

  "bipolar definitions" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += Ti; ctx += hoc"P: i>o"; ctx += hoc"Q: i>o"
    ctx += hof"D = (!x (P x | Q x))"
    val Some( d ) = ctx.updates.collectFirst { case d: Definition => d }
    val p = ProofBuilder
      .c( Input( hos":- !x (P x | Q x)" ) )
      .u( DefIntro( _, Suc( 0 ), d, Seq() ) )
      .c( Input( hos"!x (P x | Q x) :-" ) )
      .u( DefIntro( _, Ant( 0 ), d, Seq() ) )
      .b( Resolution( _, Suc( 0 ), _, Ant( 0 ) ) )
      .qed
    ctx.check( p )
    val exp = ResolutionToExpansionProof( p )
    ctx.check( exp )
    exp.shallow must_== hos"!x (P x | Q x) :- !x (P x | Q x)"
    exp.deep must beValidSequent
  }

  "bipolar definitions from common subexpression elimination" in {
    val f = Sequent() :+ CountingEquivalence( 1 )
    implicit val ctx: MutableContext = MutableContext.guess( f )
    val cnf = structuralCNF( f, cse = true )
    val Some( res ) = Escargot.getResolutionProof( cnf )
    val exp = ResolutionToExpansionProof( res )
    val desk = deskolemizeET(
      exp,
      removeCongruences = false // cut-elim becomes really slow
    )
    desk.shallow must_== f
    desk.deep must beValidSequent
  }

  "higher-order without equality" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += Ti; ctx += hoc"a: i"; ctx += hoc"b: i"
    // Leibniz equality is symmetric
    val sequent = hos"!X (X a -> X b) :- !X (X b -> X a)"
    val p1 = Input( hos":- ${sequent( Ant( 0 ) )}" )
    val p2 = Input( hos"${sequent( Suc( 0 ) )} :-" )
    val p3 = AllR( p1, Suc( 0 ), hov"X: i>o" )
    val p4 = ImpR( p3, Suc( 0 ) )
    ctx += SkolemFun( hoc"Sk: i>o", p2.conclusion( Ant( 0 ) ) )
    val p5 = AllL( p2, Ant( 0 ), le"Sk" )
    val p6 = ImpL1( p5, Ant( 0 ) )
    val p7 = ImpL2( p5, Ant( 0 ) )
    val p8 = Subst( p4, Substitution( hov"X: i>o", le"^x (-Sk x)" ) )
    val p9 = NegL( p8, Ant( 0 ) )
    val p10 = NegR( p9, Suc( 0 ) )
    val p11 = Resolution( p10, Suc( 0 ), p7, Ant( 0 ) )
    val p12 = Resolution( p6, Suc( 0 ), p11, Ant( 0 ) )
    val exp = ResolutionToExpansionProof( p12 )
    exp.shallow must_== sequent
    exp.deep must beValidSequent
  }
}
