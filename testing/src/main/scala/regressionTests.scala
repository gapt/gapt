package at.logic.gapt.testing

import java.io.File

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.expr.fol.isFOLPrenexSigma1
import at.logic.gapt.formats.leanCoP.LeanCoPParser
import at.logic.gapt.formats.veriT.VeriTParser
import at.logic.gapt.proofs.ceres.CERES
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.cutintro._
import at.logic.gapt.proofs.lkNew._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.resolution.{ simplifyResolutionProof, RobinsonToLK, RobinsonToExpansionProof }
import at.logic.gapt.provers.minisat.MiniSATProver
import at.logic.gapt.provers.veriT.VeriTProver
import at.logic.gapt.provers.prover9.{ Prover9Importer, Prover9Prover }
import scala.concurrent.duration._
import scala.util.Random

import scala.xml.XML

class Prover9TestCase( f: File ) extends RegressionTestCase( f.getParentFile.getName ) {
  override def timeout = Some( 10 minutes )

  override def test( implicit testRun: TestRun ) = {
    val ( robinson, reconstructedEndSequent ) = Prover9Importer.robinsonProofWithReconstructedEndSequentFromFile( f getAbsolutePath ) --- "import"
    val p = RobinsonToLK( robinson, reconstructedEndSequent ) --- "RobinsonToLK"

    cleanStructuralRules( p ) --? "cleanStructuralRules"
    if ( isFOLPrenexSigma1( p.endSequent ) )
      extractRecSchem( p ) --? "extractRecSchem" map { recSchem =>
        new VeriTProver().isValid( recSchem.language.map( _.asInstanceOf[HOLFormula] ) ++: Sequent() ) !-- "extractRecSchem language validity"
      }

    regularize( p ) --? "regularize"
    skolemize( p ) --? "skolemize"
    LKToLKsk( p ) --? "LKToLKsk"

    val E = LKToExpansionProof( p ) --- "LKToExpansionProof"
    val deep = toDeep( E )

    simplifyResolutionProof( robinson ).conclusion.isEmpty !-- "simplifyResolutionProof"

    ( toShallow( E ) == p.endSequent ) !-- "shallow sequent of expansion proof"

    if ( !containsEqualityReasoning( p ) ) {
      new MiniSATProver().isValid( deep ) !-- "minisat validity"
      solve.solvePropositional( deep ).isDefined !-- "solvePropositional"
      ExpansionProofToLK( E ) --- "expansionProofToLKProof"
    }

    // FIXME: extend to equality
    if ( !containsEqualityReasoning( p ) ) {
      ReductiveCutElimination( p ) --? "cut-elim (input)"
    }

    new VeriTProver().isValid( deep ) !-- "verit validity"

    if ( isFOLPrenexSigma1( p.endSequent ) ) {
      ( CutIntroduction.compressLKProof( p, DeltaTableMethod( manyQuantifiers = true ), verbose = false ) --? "cut-introduction" flatten ) foreach { q =>

        if ( !containsEqualityReasoning( q ) )
          ReductiveCutElimination( q ) --? "cut-elim (cut-intro)"
        CERES( lkNew2Old( q ) ) --? "CERES (cut-intro)"
      }
    }

    RobinsonToExpansionProof( robinson, reconstructedEndSequent ) --? "RobinsonToExpansionProof" map { E2 =>
      new VeriTProver().isValid( toDeep( E2 ) ) !-- "toDeep validity of RobinsonToExpansionProof"
      if ( isFOLPrenexSigma1( reconstructedEndSequent ) )
        new VeriTProver().isValid( extractInstances( E2 ) ) !-- "extractInstances validity of RobinsonToExpansionProof"
    }

    val ip = new Prover9Prover().getLKProof( deep ).get --- "getLKProof( deep )"
    val ( indices1, indices2 ) = ip.endSequent.indices.splitAt( ip.endSequent.size / 2 )
    ExtractInterpolant( ip, indices1, indices2 ) --? "extractInterpolant"
    ExtractInterpolant( ip, indices2, indices1 ) --? "extractInterpolant diff partition"
  }
}

class LeanCoPTestCase( f: File ) extends RegressionTestCase( f.getParentFile.getName ) {
  override def timeout = Some( 2 minutes )

  override def test( implicit testRun: TestRun ) = {
    val E = LeanCoPParser.getExpansionProof( f.getAbsolutePath ).get --- "import"

    val deep = toDeep( E ) --- "toDeep"
    new VeriTProver().isValid( deep.toFormula ) !-- "verit validity"
  }
}

class VeriTTestCase( f: File ) extends RegressionTestCase( f.getName ) {
  override def test( implicit testRun: TestRun ) = {
    val E = addSymmetry( VeriTParser.getExpansionProof( f.getAbsolutePath ).get ) --- "import"

    val deep = toDeep( E ) --- "toDeep"
    new MiniSATProver().isValid( deep.toFormula ) !-- "minisat validity"
  }
}

// Usage: RegressionTests [<test number limit>]
object RegressionTests extends App {
  def prover9Proofs = recursiveListFiles( "testing/TSTP/prover9" )
    .filter( _.getName.endsWith( ".out" ) )

  def leancopProofs = recursiveListFiles( "testing/TSTP/leanCoP" )
    .filter( _.getName.endsWith( ".out" ) )

  def veritProofs = recursiveListFiles( "testing/veriT-SMT-LIB" )
    .filter( _.getName.endsWith( ".proof_flat" ) )

  def prover9TestCases = prover9Proofs.map( new Prover9TestCase( _ ) )
  def leancopTestCases = leancopProofs.map( new LeanCoPTestCase( _ ) )
  def veritTestCases = veritProofs.map( new VeriTTestCase( _ ) )

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
  val results = testCases.par map { tc =>
    started += 1
    println( s"[${( 100 * started ) / total}%] $tc" )
    try runOutOfProcess( Seq( "-Xmx1G", "-Xss30m" ) ) {
      tc.run().toJUnitXml
    } catch {
      case t: Throwable =>
        println( s"$tc failed:" )
        t.printStackTrace()
        <testsuite/>
    }
  }

  XML.save(
    "target/regression-test-results.xml",
    <testsuite> { results flatMap ( _.child ) toList } </testsuite>,
    "UTF-8"
  )
}
