package at.logic.gapt.testing

import java.io.{ FileWriter, File }

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.expr.fol.isFOLPrenexSigma1
import at.logic.gapt.formats.leanCoP.LeanCoPParser
import at.logic.gapt.formats.veriT.VeriTParser
import at.logic.gapt.proofs.ceres.CERES
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.cutintro._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.resolution.{ simplifyResolutionProof, RobinsonToLK, RobinsonToExpansionProof }
import at.logic.gapt.provers.sat.MiniSAT
import at.logic.gapt.provers.veriT.VeriT
import at.logic.gapt.provers.prover9.{ Prover9Importer, Prover9 }
import at.logic.gapt.utils.glob
import scala.concurrent.duration._
import scala.util.Random

import scala.xml.XML

class Prover9TestCase( f: File ) extends RegressionTestCase( f.getParentFile.getName ) {
  override def timeout = Some( 10 minutes )

  override def test( implicit testRun: TestRun ) = {
    val ( robinson, reconstructedEndSequent ) = Prover9Importer.robinsonProofWithReconstructedEndSequentFromFile( f getAbsolutePath ) --- "import"

    RobinsonToExpansionProof( robinson, reconstructedEndSequent ) --? "RobinsonToExpansionProof" map { E2 =>
      VeriT.isValid( toDeep( E2 ) ) !-- "toDeep validity of RobinsonToExpansionProof"
      VeriT.isValid( extractInstances( E2 ) ) !-- "extractInstances validity of RobinsonToExpansionProof"
    }

    val p = RobinsonToLK( robinson, reconstructedEndSequent ) --- "RobinsonToLK"

    regularize( p ) --? "regularize"
    LKToLKsk( p ) --? "LKToLKsk"

    val E = LKToExpansionProof( p ) --- "LKToExpansionProof"
    val deep = toDeep( E )

    simplifyResolutionProof( robinson ).conclusion.isEmpty !-- "simplifyResolutionProof"

    ( toShallow( E ) == p.endSequent ) !-- "shallow sequent of expansion proof"

    val ip = Prover9.getLKProof( deep ).get --- "getLKProof( deep )"
    val ( indices1, indices2 ) = ip.endSequent.indices.splitAt( ip.endSequent.size / 2 )
    ExtractInterpolant( ip, indices1, indices2 ) --? "extractInterpolant"
    ExtractInterpolant( ip, indices2, indices1 ) --? "extractInterpolant diff partition"

    if ( !containsEqualityReasoning( p ) ) {
      MiniSAT.isValid( deep ) !-- "minisat validity"
      solve.solvePropositional( deep ).isDefined !-- "solvePropositional"
      ExpansionProofToLK( E ) --- "expansionProofToLKProof"
    }
    VeriT.isValid( deep ) !-- "verit validity"

    if ( isFOLPrenexSigma1( p.endSequent ) )
      extractRecSchem( p ) --? "extractRecSchem" map { recSchem =>
        VeriT.isValid( Sequent() :++ recSchem.languageWithDummyParameters.map( _.asInstanceOf[HOLFormula] ) ) !-- "extractRecSchem language validity"
      }

    // FIXME: extend to equality
    if ( !containsEqualityReasoning( p ) ) {
      ReductiveCutElimination( p ) --? "cut-elim (input)"
    }

    cleanStructuralRules( p ) --? "cleanStructuralRules"

    if ( isFOLPrenexSigma1( p.endSequent ) )
      ( CutIntroduction.compressLKProof( p, DeltaTableMethod( manyQuantifiers = true ), verbose = false ) --? "cut-introduction" flatten ) foreach { q =>

        if ( !containsEqualityReasoning( q ) )
          ReductiveCutElimination( q ) --? "cut-elim (cut-intro)"
        CERES( q ) --? "CERES (cut-intro)"

        VeriT.isValid( Sequent() :++ extractRecSchem( q ).languageWithDummyParameters.map( _.asInstanceOf[HOLFormula] ) ) !-- "extractRecSchem validity (cut-intro)"
      }

    skolemize( p ) --? "skolemize"
  }
}

class LeanCoPTestCase( f: File ) extends RegressionTestCase( f.getParentFile.getName ) {
  override def timeout = Some( 2 minutes )

  override def test( implicit testRun: TestRun ) = {
    val E = LeanCoPParser.getExpansionProof( f.getAbsolutePath ).get --- "import"

    val deep = toDeep( E ) --- "toDeep"
    VeriT.isValid( deep.toFormula ) !-- "verit validity"
  }
}

class VeriTTestCase( f: File ) extends RegressionTestCase( f.getName ) {
  override def test( implicit testRun: TestRun ) = {
    val E = addSymmetry( VeriTParser.getExpansionProof( f.getAbsolutePath ).get ) --- "import"

    val deep = toDeep( E ) --- "toDeep"
    MiniSAT.isValid( deep.toFormula ) !-- "minisat validity"
  }
}

// Usage: RegressionTests [<test number limit>]
object RegressionTests extends App {
  def prover9Proofs = glob( "testing/TSTP/prover9/**/*.s.out" )
  def leancopProofs = glob( "testing/TSTP/leanCoP/**/*.out" )
  def veritProofs = glob( "testing/veriT-SMT-LIB/**/*.proof_flat" )

  def prover9TestCases = prover9Proofs map { fn => new Prover9TestCase( new File( fn ) ) }
  def leancopTestCases = leancopProofs map { fn => new LeanCoPTestCase( new File( fn ) ) }
  def veritTestCases = veritProofs map { fn => new VeriTTestCase( new File( fn ) ) }

  def allTestCases = prover9TestCases ++ leancopTestCases ++ veritTestCases

  def findTestCase( pat: String ) = allTestCases.find( _.toString.contains( pat ) ).get

  val testCases = args match {
    case Array( limit ) =>
      println( s"Only running $limit random tests." )
      Random.shuffle( allTestCases ).take( limit toInt )
    case _ => Random.shuffle( allTestCases )
  }

  val total = testCases.length
  var started = 0
  val out = new FileWriter( "target/regression-test-results.xml" )
  out write "<testsuite>\n"
  testCases.par foreach { tc =>
    started += 1
    println( s"[${( 100 * started ) / total}%] $tc" )
    try {
      val res = runOutOfProcess( Seq( "-Xmx1G", "-Xss30m" ) ) { tc.run().toJUnitXml }
      out.synchronized { XML.write( out, res, enc = "", xmlDecl = false, doctype = null ); out.flush() }
    } catch {
      case t: Throwable =>
        println( s"$tc failed:" )
        t.printStackTrace()
    }
  }
  out write "</testsuite>\n"
  out.close()
}
