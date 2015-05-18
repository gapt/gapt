package at.logic.gapt.testing

import java.io.File

import at.logic.gapt.cli.GAPScalaInteractiveShellLibrary.loadProver9LKProof
import at.logic.gapt.formats.veriT.VeriTParser
import at.logic.gapt.proofs.algorithms.herbrandExtraction.extractExpansionSequent
import at.logic.gapt.proofs.expansionTrees.toDeep
import at.logic.gapt.proofs.lk.algorithms.{ solve, containsEqualityReasoning }
import at.logic.gapt.provers.minisat.MiniSATProver
import at.logic.gapt.provers.veriT.VeriTProver
import scala.concurrent.duration._
import scala.util.Random

import scala.xml.XML

class Prover9TestCase( f: File ) extends RegressionTestCase( f.getParentFile.getName ) {
  override def timeout = Some( 10 minutes )

  override def test( implicit testRun: TestRun ) = {
    val p = loadProver9LKProof( f.getAbsolutePath ) --- "import"

    val E = extractExpansionSequent( p, false ) --- "extractExpansionSequent"
    val deep = toDeep( E ) --- "toDeep"

    if ( !containsEqualityReasoning( p ) ) {
      new MiniSATProver().isValid( deep ) !-- "minisat validity"

      solve.solvePropositional( deep ).isDefined !-- "solvePropositional"
      solve.expansionProofToLKProof( E ).isDefined !-- "expansionProofToLKProof"
    }
    new VeriTProver().isValid( deep ) !-- "verit validity"
  }
}

class VeriTTestCase( f: File ) extends RegressionTestCase( f.getName ) {
  override def test( implicit testRun: TestRun ) = {
    val E = VeriTParser.getExpansionProof( f.getAbsolutePath ).get --- "import"

    val deep = toDeep( E ) --- "toDeep"
    new MiniSATProver().isValid( deep.toFormula ) !-- "minisat validity"
  }
}

// Usage: RegressionTests [<test number limit>]
object RegressionTests extends App {
  def prover9Proofs = recursiveListFiles( "testing/TSTP/prover9" )
    .filter( _.getName.endsWith( ".out" ) )

  def veritProofs = recursiveListFiles( "testing/veriT-SMT-LIB" )
    .filter( _.getName.endsWith( ".proof_flat" ) )

  val prover9TestCases = prover9Proofs.map( new Prover9TestCase( _ ) )
  val veritTestCases = veritProofs.map( new VeriTTestCase( _ ) )

  val allTestCases = prover9TestCases ++ veritTestCases

  val testCases = args match {
    case Array( limit ) =>
      println( s"Only running $limit random tests." )
      Random.shuffle( allTestCases ).take( limit toInt )
    case _ => allTestCases
  }

  val total = testCases.length
  var started = 0
  val results = testCases.par map { tc =>
    started += 1
    println( s"[${( 100 * started ) / total}%] $tc" )
    try {
      tc.runOutOfProcessToJUnitXML()
    } catch {
      case t: Throwable =>
        t.printStackTrace()
        <testsuite/>
    }
  }

  XML.save( "target/regression-test-results.xml",
    <testsuite> { results flatMap ( _.child ) toList } </testsuite>,
    "UTF-8" )
}
