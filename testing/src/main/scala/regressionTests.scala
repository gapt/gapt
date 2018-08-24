package gapt.testing

import java.io.{ FileWriter, PrintWriter }

import ammonite.ops._
import gapt.cutintro._
import gapt.expr._
import gapt.expr.fol.isFOLPrenexSigma1
import gapt.formats.babel.BabelParser
import gapt.formats.leancop.LeanCoPParser
import gapt.formats.tip.TipSmtImporter
import gapt.formats.tptp.TptpImporter
import gapt.formats.verit.VeriTParser
import gapt.proofs.Context.ProofNames
import gapt.proofs.ceres._
import gapt.proofs.expansion._
import gapt.proofs.gaptic.{ ProofState, now }
import gapt.proofs.lk._
import gapt.proofs.resolution.{ ResolutionToExpansionProof, ResolutionToLKProof, simplifyResolutionProof }
import gapt.proofs.{ MutableContext, Suc, loadExpansionProof }
import gapt.provers.congruence.SimpleSmtSolver
import gapt.provers.escargot.Escargot
import gapt.provers.prover9.Prover9Importer
import gapt.provers.sat.{ MiniSAT, Sat4j }
import gapt.provers.smtlib.{ SmtInterpol, Z3 }
import gapt.provers.verit.VeriT
import gapt.provers.viper.grammars.EnumeratingInstanceGenerator
import gapt.provers.viper.{ Viper, ViperOptions }
import gapt.utils.EitherHelpers._
import gapt.utils._

import scala.concurrent.duration._
import scala.util.Random
import scala.xml.XML

class TipTestCase( f: java.io.File ) extends RegressionTestCase( f.getParentFile.getName + "/" + f.getName ) {
  override def timeout = Some( 10 minutes )

  override protected def test( implicit testRun: TestRun ): Unit = {
    val bench = TipSmtImporter.fixupAndLoad( f ) --- "tip parser"

    implicit val ctx: MutableContext = bench.ctx.newMutable
    val sequent = bench.toSequent
    val lkProofWithSk = Viper.getStrategies( sequent, ViperOptions() ).reverse.view.flatMap {
      case ( duration, strategy ) =>
        try {
          ( withTimeout( duration ) { strategy.andThen( now )( ProofState( sequent ) ) } match {
            case Left( error )         => throw new Exception( error.toSigRelativeString )
            case Right( ( _, state ) ) => state.result
          } ) --? s"viper $strategy"
        } catch {
          case _: TimeOutException =>
            // Nested withTimeout calls are just fundamentally broken.
            None
          case _: OutOfMemoryError | _: StackOverflowError =>
            None
        }
    }.headOption.getOrElse( throw new TimeOutException( null, Duration.Inf ) ) --- "viper"

    ctx.check( lkProofWithSk ) --? "checking proof against context"

    val expProofWithSk = LKToExpansionProof( lkProofWithSk ) --- "LKToExpansionProof"
    val expProofDesk = deskolemizeET( expProofWithSk ) --- "deskolemization"
    expProofWithSk.shallow.isSubsetOf( expProofDesk.shallow ) !-- "shallow sequent of deskolemization"
    Z3.isValid( expProofDesk.deep ) !-- "deskolemized deep formula validity"
    val proof = ExpansionProofToLK( expProofDesk ).get --- "ExpansionProofToLK on deskolemization"

    ctx.check( proof ) --? "checking deskolemized proof against context"

    extractRecSchem( proof ) --? "extract recursion scheme"

    LKToND( proof ) --? "LKToND"

    val All.Block( variables, _ ) = sequent.succedent.head
    val instanceTerms = new EnumeratingInstanceGenerator( variables.map( _.ty.asInstanceOf[TBase] ), ctx ).
      generate( lower = 2, upper = 3, num = 1 ).head --- "random instance term"
    val instProof = instanceProof( proof, instanceTerms )

    val proofName @ Apps( proofNameC @ Const( proofNameStr, _, _ ), _ ) =
      Atom( ctx.newNameGenerator.fresh( "proof" ), variables )
    ArithmeticInductionToSchema( proof, proofName ) --? "induction to schema" foreach { _ =>
      ProofLink( proofName ) --? "create schema proof link"
      instantiateProof.Instantiate( proofNameC( instanceTerms ) ) --? "schema instance"
      SchematicStruct( proofNameStr ).get --? "schematic struct" foreach { schemaStruct =>
        CharFormPRP.PR( CharFormPRP( schemaStruct ) ) --? "characteristic formula"
        InstanceOfSchematicStruct( CLS(
          proofNameC( instanceTerms ),
          proof.endSequent.map( _ => false ) ), schemaStruct ) --? "struct instance"
      }
    }

    normalizeLKt.inductionLK( instProof, debugging = true ) --? "eliminate inductions in instance proof using lkt"
    inductionNormalForm( instProof ) --? "eliminate inductions in instance proof" foreach { indFreeProof =>
      indFreeProof.endSequent.multiSetEquals( instProof.endSequent ) !-- "induction elimination does not modify end-sequent"
      isInductionFree( indFreeProof ) !-- "induction elimination returns induction free proof"
    }
  }

  private def isInductionFree( proof: LKProof ) =
    proof.subProofs.forall {
      case InductionRule( _, _, _ ) => false
      case _                        => true
    }
}

object TheoryTestCase {
  import gapt.examples.theories._
  object AllTheories extends Theory(
    logic,
    set,
    props,
    nat,
    natdivisible,
    natdivision,
    natorder,
    list,
    listlength,
    listfold,
    listdrop,
    natlists,
    fta )
}
class TheoryTestCase( name: String, combined: Boolean )
  extends RegressionTestCase( name + ( if ( combined ) "-combined" else "" ) ) {
  override def timeout = Some( 5 minutes )

  override protected def test( implicit testRun: TestRun ): Unit = {
    import TheoryTestCase.AllTheories._
    val lemmaHandle = LemmaHandle( ctx.get[ProofNames].names( name )._1 )
    val proof = ( if ( combined ) lemmaHandle.combined() else lemmaHandle.proof ) --- "proof"

    LKToND( proof ) --? "LKToND"
    normalizeLKt.withDebug( proof ) --? "lkt cut-elim"

    LKToExpansionProof( proof ) --? "LKToExpansionProof" foreach { expansion =>
      ExpansionProofToLK( expansion ).get --? "ExpansionProofToLK" foreach { expansionLK =>
        expansionLK.conclusion.isSubsetOf( proof.conclusion ) !-- "conclusion of ExpansionProofToLK"
        ctx.check( expansionLK ) --? "context check of ExpansionProofToLK"
        normalizeLKt.withDebug( expansionLK ) --? "lkt cut-elim (expansion)"
        LKToND( expansionLK ) --? "LKToND (expansion)"
      }
    }

    val All.Block( variables, _ ) = proof.endSequent.succedent.head
    val instanceTerms = new EnumeratingInstanceGenerator( variables.map( _.ty.asInstanceOf[TBase] ), ctx ).
      generate( lower = 2, upper = 3, num = 1 ).head --- "random instance term"
    val instProof = instanceProof( proof, instanceTerms )

    {
      implicit val mctx: MutableContext = ctx.newMutable
      val proofName @ Apps( proofNameC @ Const( proofNameStr, _, _ ), _ ) =
        Atom( mctx.newNameGenerator.fresh( "proof" ), variables )
      ArithmeticInductionToSchema( proof, proofName ) --? "induction to schema" foreach { _ =>
        ProofLink( proofName ) --? "create schema proof link"
        instantiateProof.Instantiate( proofNameC( instanceTerms ) ) --? "schema instance"
        SchematicStruct( proofNameStr ).get --? "schematic struct" foreach { schemaStruct =>
          CharFormPRP.PR( CharFormPRP( schemaStruct ) ) --? "characteristic formula"
          InstanceOfSchematicStruct( CLS( proofNameC( instanceTerms ), proof.endSequent.map( _ => false ) ), schemaStruct ) --? "struct instance"
        }
      }
    }

    normalizeLKt.inductionLK( instProof, debugging = true ) --? "eliminate inductions in instance proof using lkt"
    inductionNormalForm( instProof ) --? "eliminate inductions in instance proof" foreach { indFreeProof =>
      indFreeProof.endSequent.multiSetEquals( instProof.endSequent ) !-- "induction elimination does not modify end-sequent"
    }
  }
}

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

    val E = LKToExpansionProof( p ) --- "LKToExpansionProof"
    val deep = E.deep

    simplifyResolutionProof( robinson ).conclusion.isEmpty !-- "simplifyResolutionProof"

    ( E.shallow == p.endSequent ) !-- "shallow sequent of expansion proof"

    LKToND( p ) --? "LKToND"

    Escargot.getLKProof( deep ).get --? "getLKProof( deep )" foreach { ip =>
      val ( indices1, indices2 ) = ip.endSequent.indices.splitAt( ip.endSequent.size / 2 )
      ExtractInterpolant( ip, indices1 ) --? "extractInterpolant"
      ExtractInterpolant( ip, indices2 ) --? "extractInterpolant diff partition"
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
    SmtInterpol.isValid( deep ) !-- "validity of deep formula (SmtInterpol)"
    SimpleSmtSolver.isValid( deep ) !-- "SimpleSmtSolver on deep formula"

    if ( isFOLPrenexSigma1( p.endSequent ) )
      extractRecSchem( p ) --? "extractRecSchem" map { recSchem =>
        Z3.isUnsat( And( recSchem.languageWithDummyParameters ) ) !-- "extractRecSchem language validity"
      }

    cutNormal( p ) --? "cut-elim (input)"
    normalizeLKt.withDebug( p ) --? "lkt cut-elim (input)"

    cleanStructuralRules( p ) --? "cleanStructuralRules"

    if ( isFOLPrenexSigma1( p.endSequent ) )
      ( CutIntroduction( p ) --? "cut-introduction" flatten ) foreach { q =>
        val focus = if ( p.endSequent.succedent.isEmpty ) None else Some( Suc( 0 ) )
        LKToND( q, focus ) --? "LKToND (cut-intro)"

        cutNormal( q ) --? "cut-elim (cut-intro)"
        normalizeLKt.withDebug( q ) --? "lkt cut-elim (cut-intro)"
        CERES( q ) --? "CERES (cut-intro)"
        CERES.expansionProof( q ) --? "CERESExpansionProof"

        LKToExpansionProof( q ) --? "LKToExpansionProof (cut-intro)" foreach { expQ =>
          Z3.isValid( expQ.deep ) !-- "expansion tree validity with cut (cut-intro)"
          eliminateCutsET( expQ ) --? "expansion tree cut-elimination (cut-intro)" foreach { expQstar =>
            Z3.isValid( expQstar.deep ) !-- "cut-elim expansion tree validity (cut-intro)"
          }
          ExpansionProofToLK( expQ ).isRight !-- "ExpansionProofToLK (cut-intro)"
        }

        Z3.isUnsat( And( extractRecSchem( q ).languageWithDummyParameters ) ) !-- "extractRecSchem validity (cut-intro)"
      }

    folSkolemize( p ) --? "skolemize"
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

class TptpTestCase( f: java.io.File ) extends RegressionTestCase( f.getName ) {
  override def timeout = Some( 2 minutes )

  override def test( implicit testRun: TestRun ) = {
    val tptpDir = Path( f ) / up / up / up
    val tptpProblem = TptpImporter.loadWithIncludes( f, path => TptpImporter.loadWithoutIncludes( tptpDir / RelPath( path ) ) ) --- "TptpParser"

    val sequent = tptpProblem.toSequent

    val resolution = Escargot.getResolutionProof( sequent ).get --- "Escargot"

    val expansion = ResolutionToExpansionProof( resolution ) --- "ResolutionToExpansionProof"

    deskolemizeET( expansion ) --? "deskolemization" foreach { desk =>
      desk.shallow.isSubsetOf( expansion.shallow ) !-- "shallow sequent of deskolemization"
      Z3.isValid( desk.deep ) !-- "deskolemized deep formula validity"
      ExpansionProofToLK( desk ).get --? "ExpansionProofToLK on deskolemization" foreach { deskLK =>
        LKToND( deskLK ) --? "LKToND (deskolemization)"
      }
    }
  }
}

// Usage: RegressionTests [<test number limit>]
object RegressionTests extends scala.App {
  def prover9Proofs = ls.rec( pwd / "testing" / "TSTP" / "prover9" ).filter( _.ext == "s" )
  def leancopProofs = ls.rec( pwd / "testing" / "TSTP" / "leanCoP" ).filter( _.ext == "s" )
  def veritProofs = ls.rec( pwd / "testing" / "veriT-SMT-LIB" ).filter( _.ext == "proof_flat" )
  def tptpProblems = ls.rec( pwd / "testing" / "TPTP" / "Problems" ).filter( _.ext == "p" )
  def tipProblems = ls.rec( pwd / "testing" / "TIP" ).filter( _.ext == "smt2" )

  def prover9TestCases = prover9Proofs map { fn => new Prover9TestCase( fn.toIO ) }
  def leancopTestCases = leancopProofs map { fn => new LeanCoPTestCase( fn.toIO ) }
  def veritTestCases = veritProofs map { fn => new VeriTTestCase( fn.toIO ) }
  def tptpTestCases = tptpProblems.map { fn => new TptpTestCase( fn.toIO ) }
  def tipTestCases = tipProblems.map { fn => new TipTestCase( fn.toIO ) }
  def theoryTestCases =
    for {
      ( n, _ ) <- TheoryTestCase.AllTheories.allProofs
      combined <- Seq( false, true )
    } yield new TheoryTestCase( n, combined )

  def allTestCases =
    prover9TestCases ++
      leancopTestCases ++
      veritTestCases ++
      tptpTestCases ++
      tipTestCases ++
      theoryTestCases

  def findTestCase( pat: String ) = allTestCases.find( _.toString.contains( pat ) ).get

  val testCases = args match {
    case Array( limit ) =>
      println( s"Only running $limit random tests." )
      Random.shuffle( allTestCases ).take( limit toInt )
    case _ => Random.shuffle( allTestCases )
  }

  val total = testCases.length
  var started = 0
  val out = new PrintWriter( new FileWriter( pwd / "target" / "regression-test-results.xml" toIO ), true )
  try {
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
  } finally out.close()
}