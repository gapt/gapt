/** 
 * Description: 
**/

package at.logic.integration_tests

import at.logic.parsing.language.tptp.TPTPFOLExporter
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols._
import at.logic.language.fol._
import at.logic.language.hol.logicSymbols._
import at.logic.transformations.ceres.struct.StructCreators
import at.logic.transformations.ceres.clauseSets.StandardClauseSet
import at.logic.parsing.language.xml.XMLParser._
import at.logic.parsing.readers.XMLReaders._
import at.logic.algorithms.lk.simplification._
import at.logic.algorithms.lk.statistics._
import at.logic.algorithms.lk._
import at.logic.parsing.calculus.xml.saveXML
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.macroRules._
import at.logic.algorithms.lk.simplification._
import at.logic.algorithms.lk._
import java.util.zip.GZIPInputStream
import java.io.{FileReader, FileInputStream, InputStreamReader}
import java.io.File.separator
import at.logic.transformations.skolemization.skolemize
import at.logic.transformations.ceres.projections.Projections
import at.logic.transformations.ceres.clauseSets.profile._
import at.logic.calculi.occurrences._
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import org.specs2.execute.Success
import at.logic.algorithms.cutIntroduction._
import at.logic.transformations.ReductiveCutElim

@RunWith(classOf[JUnitRunner])
class MiscTest extends SpecificationWithJUnit {

  // returns LKProof with end-sequent  P(s^k(0)), \ALL x . P(x) -> P(s(x)) :- P(s^n(0))
  private def LinearExampleProof( k : Int, n : Int ) : LKProof = {
    val s = new ConstantStringSymbol("s")
    val c = new ConstantStringSymbol("0")
    val p = new ConstantStringSymbol("P")

    val x = FOLVar( VariableStringSymbol("x") )
    val ass = AllVar( x, Imp( Atom( p, x::Nil ), Atom( p, Function( s, x::Nil )::Nil ) ) )
    if ( k == n ) // leaf proof
    {
      val a = Atom( p,  Utils.numeral( n )::Nil )
      WeakeningLeftRule( Axiom( a::Nil, a::Nil ), ass )
    }
    else
    {
      val p1 = Atom( p, Utils.numeral( k )::Nil )
      val p2 = Atom( p, Utils.numeral( k + 1 )::Nil )
      val aux = Imp( p1, p2 )
      ContractionLeftRule( ForallLeftRule( ImpLeftRule( Axiom( p1::Nil, p1::Nil ), LinearExampleProof( k + 1, n ), p1, p2 ), aux, ass, Utils.numeral( k ) ), ass )
    }
  }

  "The system" should {
    /*
//    "parse, skolemize, extract clause set for a simple induction proof" in {
//      val proofs = (new XMLReader(new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "simple_ind.xml"))) with XMLProofDatabaseParser)..getProofDatabase()
//      proofs.size must beEqualTo(1)
//      val proof = proofs.first
//      val proof_sk = LKtoLKskc( proof )
//      val s = StructCreators.extract( proof_sk )
//      val cs = StandardClauseSet.transformStructToClauseSet( s )
//      val dcs = deleteTautologies( cs )
//      val css = setNormalize( dcs )
//      val cs_path = "target" + separator + "test-classes" + separator + "simple_ind-cs.xml"
//      saveXML( Pair("cs", cs)::Pair("dcs", dcs)::Pair("css", (css.toList))::Nil, cs_path )
//      (new java.io.File( cs_path ) ).exists() must beEqualTo( true )
//    }
//    */

    "skolemize a simple proof" in {
      val proofdb = (new XMLReader(new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "sk2.xml"))) with XMLProofDatabaseParser).getProofDatabase()
      proofdb.proofs.size must beEqualTo(1)
      val proof = proofdb.proofs.head._2
      val proof_sk = skolemize( proof )
      //println("skolemized proof:")
      //println(proof_sk)
      Success()
    }

    "skolemize a proof with a simple definition" in {
      val proofdb = (new XMLReader(new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "sk3.xml"))) with XMLProofDatabaseParser).getProofDatabase()
      proofdb.proofs.size must beEqualTo(1)
      val proof = proofdb.proofs.head._2
      val proof_sk = skolemize( proof )
      //println("skolemized proof:")
      //println(proof_sk)
      Success()
    }

    "skolemize a proof with a complex definition" in {
      val proofdb = (new XMLReader(new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "sk4.xml"))) with XMLProofDatabaseParser).getProofDatabase()
      proofdb.proofs.size must beEqualTo(1)
      val proof = proofdb.proofs.head._2
      val proof_sk = skolemize( proof )
      //println("skolemized proof:")
      //println(proof_sk)
      Success()
    }

    "extract projections and clause set from a skolemized proof" in {
      val proofdb = (new XMLReader(new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "test1p.xml"))) with XMLProofDatabaseParser).getProofDatabase()
      proofdb.proofs.size must beEqualTo(1)
      val proof = proofdb.proofs.head._2
      val projs = Projections( proof )
      val s = at.logic.transformations.ceres.struct.StructCreators.extract( proof )
      val cs = StandardClauseSet.transformStructToClauseSet( s ).map( _.toFSequent )
      val prf = deleteTautologies(proofProfile(s, proof).map( _.toFSequent ))
      val path = "target" + separator + "test-classes" + separator + "test1p-out.xml"
      saveXML( //projs.map( p => p._1 ).toList.zipWithIndex.map( p => Pair( "\\psi_{" + p._2 + "}", p._1 ) ),
        projs.toList.zipWithIndex.map( p => Pair( "\\psi_{" + p._2 + "}", p._1 ) ),
        Pair("cs", cs)::Pair("prf", prf)::Nil, path )
      Success()
    }

/*
    //Cvetan
    "extract the profile of Bruno's thesis" in {
      println("\n\n\n")
      val A: HOLFormula = Atom(new ConstantStringSymbol("A"), List())
      val B: HOLFormula = Atom(new ConstantStringSymbol("B"), List())
      val C: HOLFormula = Atom(new ConstantStringSymbol("C"), List())


      val ax1 = Axiom(A::Nil, A::Nil)
      val ax2 = Axiom(B::Nil, B::Nil)
      val ax3 = Axiom(B::Nil, B::Nil)
      val ax4 = Axiom(A::Nil, A::Nil)
      val ax5 = Axiom(C::Nil, C::Nil)
//      val ax6 = Axiom(Sequent(C::Nil, C::Nil))(PointerFOFactoryInstance)
      val r1 = AndRightRule(ax1,ax2,A,B)//.asInstanceOf[LKProof]
      var r2 = AndLeftRule(r1,A,B)
      val r3 = AndRightRule(ax3,ax4,B,A)
      var r4 = AndLeftRule(r3,A,B)
      val r5 = CutRule(r2,r4, And(A,B))
      val r6 = ax5//CutRule(ax5,ax6, C)
      val proof = OrLeftRule(r5,r6, And(A,B), C)

      val s = StructCreators.extract( proof )
      val prf = deleteTautologies(proofProfile(s, proof).map( _.toFSequent ))
      val cs = StandardClauseSet.transformStructToClauseSet( s ).map( _.toFSequent )

      // specs2 require a least one Result, see org.specs2.specification.Example 
      Success()
      // TODO: check if profile is really as expected.
    }
*/

    "introduce a cut and eliminate it via Gentzen in the LinearExampleProof (n = 4)" in {
      val p = LinearExampleProof( 0, 4 )
      val pi = CutIntroduction(p)
      val pe = ReductiveCutElim.eliminateAllByUppermost(pi, false)

      ReductiveCutElim.isCutFree(p) must beEqualTo( true )
      ReductiveCutElim.isCutFree(pi) must beEqualTo( false )
      ReductiveCutElim.isCutFree(pe) must beEqualTo( true )
    }
  }
}
