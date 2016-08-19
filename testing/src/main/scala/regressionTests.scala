package at.logic.gapt.testing

import at.logic.gapt.expr.{ And, HOLFormula }
import at.logic.gapt.expr.fol.isFOLPrenexSigma1
import at.logic.gapt.formats.babel.BabelParser
import at.logic.gapt.formats.leancop.LeanCoPParser
import at.logic.gapt.formats.verit.VeriTParser
import at.logic.gapt.grammars.DeltaTableMethod
import at.logic.gapt.proofs.ceres.CERES
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.cutintro._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.{ Sequent, loadExpansionProof }
import at.logic.gapt.proofs.resolution.{ ResolutionToExpansionProof, ResolutionToLKProof, simplifyResolutionProof }
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.sat.{ MiniSAT, Sat4j }
import at.logic.gapt.provers.verit.VeriT
import at.logic.gapt.provers.prover9.Prover9Importer
import at.logic.gapt.provers.smtlib.Z3

import scala.concurrent.duration._
import scala.util.Random
import scala.xml.XML
import better.files._

class Prover9TestCase( f: java.io.File ) extends RegressionTestCase( f.getParentFile.getName ) {
  override def timeout = Some( 3 minutes )

  override def test( implicit testRun: TestRun ) = {
    val ( robinson, reconstructedEndSequent ) = Prover9Importer.robinsonProofWithReconstructedEndSequent( f ) --- "import"

    ResolutionToExpansionProof( robinson ) --? "RobinsonToExpansionProof" map { E2 =>
      Z3.isValid( E2.deep ) !-- "toDeep validity of RobinsonToExpansionProof"
      Z3.isValid( extractInstances( E2 ) ) !-- "extractInstances validity of RobinsonToExpansionProof"
    }

    BabelParser.parse( reconstructedEndSequent.toImplication.toString ) == reconstructedEndSequent.toImplication !-- "babel round-trip"

    val p = WeakeningContractionMacroRule( ResolutionToLKProof( robinson ), reconstructedEndSequent ) --- "RobinsonToLK"

    regularize( p ) --? "regularize"
    LKToLKsk( p ) --? "LKToLKsk"

    val E = LKToExpansionProof( p ) --- "LKToExpansionProof"
    val deep = E.deep

    simplifyResolutionProof( robinson ).conclusion.isEmpty !-- "simplifyResolutionProof"

    ( E.shallow == p.endSequent ) !-- "shallow sequent of expansion proof"

    Escargot.getLKProof( deep ).get --? "getLKProof( deep )" foreach { ip =>
      val ( indices1, indices2 ) = ip.endSequent.indices.splitAt( ip.endSequent.size / 2 )
      ExtractInterpolant( ip, indices1, indices2 ) --? "extractInterpolant"
      ExtractInterpolant( ip, indices2, indices1 ) --? "extractInterpolant diff partition"
    }

    if ( !containsEqualityReasoning( p ) ) {
      MiniSAT.isValid( deep ) !-- "minisat validity"
      Sat4j.getResolutionProof( deep ).isDefined !-- "Sat4j proof import"
      solvePropositional( deep ).isRight !-- "solvePropositional"
    } else {
      solveQuasiPropositional( deep ).isRight !-- "solveQuasiPropositional"
    }
    ExpansionProofToLK( E ).isRight !-- "expansionProofToLKProof"
    Z3.isValid( deep ) !-- "validity of deep formula"

    if ( isFOLPrenexSigma1( p.endSequent ) )
      extractRecSchem( p ) --? "extractRecSchem" map { recSchem =>
        Z3.isUnsat( And( recSchem.languageWithDummyParameters ) ) !-- "extractRecSchem language validity"
      }

    // FIXME: extend to equality
    if ( !containsEqualityReasoning( p ) ) {
      ReductiveCutElimination( p ) --? "cut-elim (input)"
    }

    cleanStructuralRules( p ) --? "cleanStructuralRules"

    if ( isFOLPrenexSigma1( p.endSequent ) )
      ( CutIntroduction( p ) --? "cut-introduction" flatten ) foreach { q =>

        if ( !containsEqualityReasoning( q ) )
          ReductiveCutElimination( q ) --? "cut-elim (cut-intro)"
        CERES( q ) --? "CERES (cut-intro)"

        LKToExpansionProof( q ) --? "LKToExpansionProof (cut-intro)" foreach { expQ =>
          Z3.isValid( expQ.deep ) !-- "expansion tree validity with cut (cut-intro)"
          eliminateCutsET( expQ ) --? "expansion tree cut-elimination (cut-intro)" foreach { expQstar =>
            Z3.isValid( expQstar.deep ) !-- "cut-elim expansion tree validity (cut-intro)"
          }
          ExpansionProofToLK( expQ ).isRight !-- "ExpansionProofToLK (cut-intro)"
        }

        Z3.isUnsat( And( extractRecSchem( q ).languageWithDummyParameters ) ) !-- "extractRecSchem validity (cut-intro)"
      }

    skolemize( p ) --? "skolemize"
  }
}

class LeanCoPTestCase( f: java.io.File ) extends RegressionTestCase( f.getParentFile.getName ) {
  override def timeout = Some( 2 minutes )

  override def test( implicit testRun: TestRun ) = {
    val E = LeanCoPParser.getExpansionProof( loadExpansionProof.extractFromTSTPCommentsIfNecessary( f ) ).get --- "import"

    val deep = E.deep --- "toDeep"
    VeriT.isValid( deep.toDisjunction ) !-- "verit validity"
  }
}

class VeriTTestCase( f: java.io.File ) extends RegressionTestCase( f.getName ) {
  override def test( implicit testRun: TestRun ) = {
    val E = VeriTParser.getExpansionProofWithSymmetry( f ).get --- "import"

    val deep = E.deep --- "toDeep"
    MiniSAT.isValid( deep.toDisjunction ) !-- "minisat validity"
  }
}

// Usage: RegressionTests [<test number limit>]
object RegressionTests extends App {
  def prover9Proofs = file"testing/TSTP/prover9".glob( "**/*.s" ).toSeq
  def leancopProofs = file"testing/TSTP/leanCoP".glob( "**/*.s" ).toSeq
  def veritProofs = file"testing/veriT-SMT-LIB".glob( "**/*.proof_flat" ).toSeq

  def prover9TestCases = prover9Proofs map { fn => new Prover9TestCase( fn.toJava ) }
  def leancopTestCases = leancopProofs map { fn => new LeanCoPTestCase( fn.toJava ) }
  def veritTestCases = veritProofs map { fn => new VeriTTestCase( fn.toJava ) }

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
  for ( out <- file"target/regression-test-results.xml".printWriter( autoFlush = true ) ) {
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
  }
}
