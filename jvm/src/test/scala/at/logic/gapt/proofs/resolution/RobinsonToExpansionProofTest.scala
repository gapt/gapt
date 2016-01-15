package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ naive, thresholds }
import at.logic.gapt.expr.hol.{ CNFn, structuralCNF, existsclosure }
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.expansionTrees.{ toDeep, toShallow }
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.veriT.VeriT
import org.specs2.mutable._

class RobinsonToExpansionProofTest extends Specification {
  if ( !VeriT.isInstalled || !Prover9.isInstalled ) skipAll

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
      val Some( robinson ) = Prover9 getRobinsonProof es
      val expansion = RobinsonToExpansionProof( robinson )
      val deep = toDeep( expansion )
      VeriT isValid deep must_== true
    }

    "extract expansion sequent for the given end sequent" in {
      val Some( robinson ) = Prover9 getRobinsonProof es
      val expansion = RobinsonToExpansionProof( robinson, es )
      toShallow( expansion ) isSubMultisetOf es must_== true
      val deep = toDeep( expansion )
      VeriT isValid deep must_== true
    }
  }

  "tautological clauses with naive CNF" in {
    val p = FOLAtom( "p" )
    val endSequent = Sequent() :+ ( ( p --> -( -p ) ) & ( -( -p ) --> p ) )
    val cnf = CNFn.toFClauseList( endSequent.toFormula )
    val Some( robinson ) = Prover9 getRobinsonProof cnf
    val expansion = RobinsonToExpansionProof( robinson, endSequent )
    toShallow( expansion ) isSubMultisetOf endSequent must_== true
    val deep = toDeep( expansion )
    VeriT isValid deep must_== true
  }

  "complicated formula with structural CNF" should {
    val x = FOLVar( "x" )
    val Seq( c, d ) = Seq( "c", "d" ) map { FOLConst( _ ) }
    val as = ( 0 to 12 ) map { i => FOLAtomConst( s"a$i", 1 ) }
    val endSequent = thresholds.atMost.oneOf( as map { a => Ex( x, a( x ) ) } ) +: Sequent() :+ ( as( 0 )( c ) --> -as( 1 )( d ) )

    "extract expansion sequent" in {
      val ( cnf, projs, defs ) = structuralCNF( endSequent, generateJustifications = true, propositional = false )
      val Some( ref ) = Prover9 getRobinsonProof cnf
      val expansion = RobinsonToExpansionProof( ref, endSequent, projs, defs )
      toShallow( expansion ) isSubMultisetOf endSequent must_== true
      val deep = toDeep( expansion )
      VeriT isValid deep must_== true
    }
  }

  "quantified definitions" should {
    val Seq( x, y, z ) = Seq( "x", "y", "z" ) map { FOLVar( _ ) }
    val c = FOLConst( "c" )
    val as = ( 0 to 2 ) map { i => All( x, Ex( y, FOLAtom( s"a$i", x, y, z ) ) ) }
    val endSequent = Sequent() :+ ( All( z, thresholds.exactly.oneOf( as ) ) <-> All( z, naive.exactly.oneOf( as ) ) )

    "extract expansion sequent with skolem quantifiers" in {
      val ( cnf, projs, defs ) = structuralCNF( endSequent, generateJustifications = true, propositional = false )
      val Some( ref ) = Prover9 getRobinsonProof cnf
      val expansion = RobinsonToExpansionProof( ref, endSequent, projs, defs )
      toShallow( expansion ) isSubMultisetOf endSequent must_== true
      val deep = toDeep( expansion )
      VeriT isValid deep must_== true
    }
  }
}
