package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ naive, thresholds }
import at.logic.gapt.expr.hol.{ CNFn, structuralCNF, existsclosure }
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.proofs.{ SequentMatchers, Sequent }
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable._

class RobinsonToExpansionProofTest extends Specification with SatMatchers with SequentMatchers {
  "simple proof from prover9" should {
    val es = existsclosure(
      "P(c,z)" +:
        "P(x,g(z)) -> P(f(x),z) & R(y)" +:
        "P(x,z) -> Q(x)" +:
        Sequent()
        :+ "Q(f(f(x)))"
        map parseFormula
    )

    "extract expansion sequent for the initial clauses" in {
      val Some( robinson ) = Escargot getRobinsonProof es
      val expansion = RobinsonToExpansionProof( robinson )
      expansion.deep must beValidSequent
    }

    "extract expansion sequent for the given end sequent" in {
      val Some( robinson ) = Escargot getRobinsonProof es
      val expansion = RobinsonToExpansionProof( robinson, es )
      expansion.shallow must_== es
      expansion.deep must beValidSequent
    }
  }

  "tautological clauses with naive CNF" in {
    val p = FOLAtom( "p" )
    val endSequent = Sequent() :+ ( ( p --> -( -p ) ) & ( -( -p ) --> p ) )
    val cnf = CNFn.toFClauseList( endSequent.toFormula )
    val Some( robinson ) = Escargot getRobinsonProof cnf
    val expansion = RobinsonToExpansionProof( robinson, endSequent )
    expansion.shallow must_== endSequent
    expansion.deep must beValidSequent
  }

  "complicated formula with structural CNF" in {
    val x = FOLVar( "x" )
    val Seq( c, d ) = Seq( "c", "d" ) map { FOLConst( _ ) }
    val as = ( 0 to 12 ) map { i => FOLAtomConst( s"a$i", 1 ) }
    val endSequent = thresholds.atMost.oneOf( as map { a => Ex( x, a( x ) ) } ) +: Sequent() :+ ( as( 0 )( c ) --> -as( 1 )( d ) )

    val ( cnf, projs, defs ) = structuralCNF( endSequent, generateJustifications = true, propositional = false )
    val Some( ref ) = Escargot getRobinsonProof cnf
    val expansion = RobinsonToExpansionProof( ref, endSequent, projs, defs )
    expansion.shallow must_== endSequent
    expansion.deep must beValidSequent
  }

  "quantified definitions" in {
    val Seq( x, y, z ) = Seq( "x", "y", "z" ) map { FOLVar( _ ) }
    val as = ( 0 to 2 ) map { i => All( x, Ex( y, FOLAtom( s"a$i", x, y, z ) ) ) }
    val endSequent = Sequent() :+ ( All( z, thresholds.exactly.oneOf( as ) ) <-> All( z, naive.exactly.oneOf( as ) ) )

    val ( cnf, projs, defs ) = structuralCNF( endSequent, generateJustifications = true, propositional = false )
    val Some( ref ) = Escargot getRobinsonProof cnf
    val expansion = RobinsonToExpansionProof( ref, endSequent, projs, defs )
    expansion.shallow must_== endSequent
    expansion.deep must beValidSequent
  }

  "duplicate bound variables" in {
    val Seq( p, q ) = Seq( "p", "q" ) map { FOLAtomConst( _, 1 ) }
    val Seq( c, d ) = Seq( "c", "d" ) map { FOLConst( _ ) }
    val x = FOLVar( "x" )

    val endSequent = Sequent() :+ ( ( All( x, p( x ) ) | All( x, q( x ) ) ) --> ( p( c ) | q( d ) ) )

    val ( cnf, projs, defs ) = structuralCNF( endSequent, generateJustifications = true, propositional = false )
    val Some( ref ) = Escargot getRobinsonProof cnf
    val expansion = RobinsonToExpansionProof( ref, endSequent, projs, defs )
    expansion.shallow must_== endSequent
    expansion.deep must beValidSequent
  }
}
