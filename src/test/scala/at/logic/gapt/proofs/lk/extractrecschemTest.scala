package at.logic.gapt.proofs.lk

import java.io.InputStreamReader
import java.util.zip.GZIPInputStream

import at.logic.gapt.algorithms.rewriting.DefinitionElimination
import at.logic.gapt.examples.Pi2Pigeonhole
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.Utils
import at.logic.gapt.expr.hol.{ instantiate, univclosure }
import at.logic.gapt.formats.readers.XMLReaders.XMLReader
import at.logic.gapt.formats.xml.XMLParser.XMLProofDatabaseParser
import at.logic.gapt.grammars.{ HORS, HORule }
import at.logic.gapt.proofs.lk.base.{ LKProof, HOLSequent }
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.{ parseFormula, parseTerm }
import at.logic.gapt.provers.prover9.Prover9Prover
import at.logic.gapt.provers.sat4j.Sat4jProver
import at.logic.gapt.provers.veriT.VeriTProver
import org.specs2.mutable._
import org.specs2.specification.core.Fragment

class ExtractRecSchemTest extends Specification {
  "simple" in {
    val g0 = parseFormula( "P(c)" )
    val g1 = parseFormula( "(all y (P(y) -> P(f(y))))" )
    val g2 = parseFormula( "P(f(f(f(f(c)))))" )

    val p1 = solve.solvePropositional( HOLSequent(
      Seq( "P(x) -> P(f(x))", "P(f(x)) -> P(f(f(x)))" ) map parseFormula,
      Seq( "P(x) -> P(f(f(x)))" ) map parseFormula
    ) ).get
    val cutf = parseFormula( "(all z (P(z) -> P(f(f(z)))))" )
    val p2 = ForallLeftRule( p1, parseFormula( "P(x) -> P(f(x))" ), g1, parseTerm( "x" ) )
    val p3 = ForallLeftRule( p2, parseFormula( "P(f(x)) -> P(f(f(x)))" ), g1, parseTerm( "f(x)" ) )
    val p4 = ContractionMacroRule( p3 )
    val p5 = ForallRightRule( p4, parseFormula( "P(x) -> P(f(f(x)))" ), cutf, FOLVar( "x" ) )

    val q1 = solve.solvePropositional( HOLSequent(
      Seq( "P(c) -> P(f(f(c)))", "P(f(f(c))) -> P(f(f(f(f(c)))))" ) map parseFormula,
      Seq( "P(c) -> P(f(f(f(f(c)))))" ) map parseFormula
    ) ).get
    val q2 = ForallLeftRule( q1, parseFormula( "P(c) -> P(f(f(c)))" ), cutf, parseTerm( "c" ) )
    val q3 = ForallLeftRule( q2, parseFormula( "P(f(f(c))) -> P(f(f(f(f(c)))))" ), cutf, parseTerm( "f(f(c))" ) )
    val q4 = ContractionMacroRule( q3 )

    val p = CutRule( p5, q4, cutf )

    val recSchem = extractRecSchem( p )
    val lang = recSchem.language( FOLAtom( "A" ) ).map( _.asInstanceOf[HOLFormula] )

    new Sat4jProver().isValid( HOLSequent( lang.toSeq, Seq() ) ) must beTrue
  }

  "pi2 pigeonhole" in {
    val p9 = new Prover9Prover
    if ( !p9.isInstalled ) skipped

    val p = Pi2Pigeonhole()
    val recSchem = extractRecSchem( p )

    val lang = recSchem.language( FOLAtom( "A" ) ).map( _.asInstanceOf[HOLFormula] )

    p9.isValid( HOLSequent( lang.toSeq, Seq() ) ) must beTrue
  }

  "tape proof" in {
    val pdb = ( new XMLReader( new InputStreamReader( new GZIPInputStream( getClass.getClassLoader.getResourceAsStream( "tape-in.xml.gz" ) ) ) ) with XMLProofDatabaseParser ).getProofDatabase()
    val proof = DefinitionElimination( pdb.Definitions, regularize( pdb.proof( "the-proof" ) ) )

    val recSchem = extractRecSchem( proof )

    val p9 = new Prover9Prover
    if ( !p9.isInstalled ) skipped

    val lang = recSchem.language( FOLAtom( "A", FOLConst( "n_0" ) ) ).map( _.asInstanceOf[HOLFormula] )
    // the following formulas are not present in the end-sequent...
    val additionalAxioms = Seq(
      "x+(y+z) = (x+y)+z",
      "x+y = y+x",
      "x != x+(y+1)"
    ).map { s => univclosure( parseFormula( s ) ) }
    p9.isValid( HOLSequent( additionalAxioms ++ lang, Seq() ) ) must beTrue

    ok
  }

  "simple pi3" in {
    val cutf = parseFormula( "(all x (exists y (all z (P(x,y,z)))))" )

    var p1: LKProof = Axiom( parseFormula( "P(w1,w1,w2)" ) )
    p1 = ForallLeftBlock( p1, parseFormula( "(all x (all y (P(x,x,y))))" ), Seq( "w1", "w2" ) map parseTerm )
    p1 = ForallRightBlock( p1, instantiate( cutf, Seq( "w1", "w1" ) map parseTerm ), Seq( FOLVar( "w2" ) ) )
    p1 = ExistsRightBlock( p1, instantiate( cutf, Seq( "w1" ) map parseTerm ), Seq( FOLVar( "w1" ) ) )
    p1 = ForallRightBlock( p1, cutf, Seq( FOLVar( "w1" ) ) )

    var p2: LKProof = Axiom( parseFormula( "P(c,w3,d)" ) )
    p2 = ExistsRightBlock( p2, parseFormula( "(exists x (P(c,x,d)))" ), Seq( parseTerm( "w3" ) ) )
    p2 = ForallLeftBlock( p2, instantiate( cutf, Seq( "c", "w3" ) map parseTerm ), Seq( parseTerm( "d" ) ) )
    p2 = ExistsLeftRule( p2, instantiate( cutf, Seq( "c", "w3" ) map parseTerm ), FOLVar( "y" ), FOLVar( "w3" ) )
    p2 = ForallLeftBlock( p2, cutf, Seq( parseTerm( "c" ) ) )

    val p = CutRule( p1, p2, cutf )

    val recschem = extractRecSchem( p )
    println( recschem )
    recschem.language( FOLAtom( "A" ) ) foreach println
    recschem.rules map {
      case HORule( HOLAtom( head, _ ), _ ) => head
    } foreach { case Const( name, ty ) => println( s"$name: $ty" ) }

    new Sat4jProver().isValid(
      recschem.language( FOLAtom( "A" ) ).map( _.asInstanceOf[FOLFormula] ).toSeq ++: HOLSequent()
    ) must_== true
  }
}

class Pi2FactorialPOC extends Specification {
  val A = Const( "A", Ti -> To )
  val B = Const( "B", Ti -> ( Ti -> ( ( Ti -> To ) -> To ) ) )
  val C = Const( "C", Ti -> To )
  val D = Const( "D", ( Ti -> To ) -> ( Ti -> ( Ti -> ( Ti -> To ) ) ) )
  val X = Var( "X", Ti -> To )

  val hors = HORS( Set(
    HORule( parseFormula( "A(z)" ), Apps( B, FOLVar( "z" ), Utils.numeral( 1 ), C ) ),
    HORule( parseFormula( "A(z)" ), parseFormula( "s(0)*z = z" ) ),
    HORule( parseFormula( "A(z)" ), parseFormula( "f(z) != g(s(0),z)" ) ),
    HORule( parseFormula( "C(w)" ), Top() ), // FIXME: NF != generated word
    HORule(
      Apps( B, parseTerm( "s(x)" ), FOLVar( "y" ), X ),
      Apps( B, FOLVar( "x" ), parseTerm( "y*s(x)" ), Apps( D, X, FOLVar( "x" ), FOLVar( "y" ) ) )
    ),
    HORule( Apps( D, X, FOLVar( "x" ), FOLVar( "y" ), FOLVar( "w" ) ), parseFormula( "(y*s(x))*w = y*(s(x)*w)" ) ),
    HORule( Apps( D, X, FOLVar( "x" ), FOLVar( "y" ), FOLVar( "w" ) ), parseFormula( "g(y,s(x)) = g(y*s(x),x)" ) ),
    HORule( Apps( D, X, FOLVar( "x" ), FOLVar( "y" ), FOLVar( "w" ) ), parseFormula( "f(s(x)) = s(x)*f(x)" ) ),
    HORule( Apps( D, X, FOLVar( "x" ), FOLVar( "y" ), FOLVar( "w" ) ), App( X, parseTerm( "s(x)*w" ) ) ),
    HORule( Apps( B, FOLConst( "0" ), FOLVar( "y" ), X ), parseFormula( "g(y,0)=y" ) ),
    HORule( Apps( B, FOLConst( "0" ), FOLVar( "y" ), X ), parseFormula( "f(0)=s(0)" ) ),
    HORule( Apps( B, FOLConst( "0" ), FOLVar( "y" ), X ), parseFormula( "s(0)*s(0)=s(0)" ) ),
    HORule( Apps( B, FOLConst( "0" ), FOLVar( "y" ), X ), Apps( X, Utils.numeral( 1 ) ) )
  ) )

  def lang( i: Int ) = hors.language( Apps( A, Utils.numeral( i ) ) ).map( _.asInstanceOf[HOLFormula] )

  println( hors )
  println()
  lang( 3 ).toSeq.sortBy( _.toString ) foreach println
  println()

  "termination" in {
    lang( 10 )
    ok
  }

  "languages should be tautologies" in {
    val verit = new VeriTProver
    Fragment.foreach( 0 to 5 ) { i =>
      s"n = $i" in {
        if ( !verit.isInstalled ) skipped
        verit.isValid( HOLSequent( lang( i ).toSeq, Seq() ) ) must beTrue
      }
    }
  }
}