package at.logic.gapt.provers.viper

import ammonite.ops._
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.folTermSize
import at.logic.gapt.formats.tip.{ TipProblem, TipSmtParser }
import at.logic.gapt.formats.{ InputFile, StringInputFile }
import at.logic.gapt.grammars.InductionGrammar
import at.logic.gapt.proofs.{ HOLSequent, MutableContext }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.gaptic.tactics.AnalyticInductionTactic
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.prooftool.prooftool
import at.logic.gapt.provers.eprover.EProver
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.iprover.IProver
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.spass.SPASS
import at.logic.gapt.provers.vampire.Vampire
import at.logic.gapt.provers.viper.aip.axioms._
import at.logic.gapt.provers.ResolutionProver
import at.logic.gapt.provers.viper.grammars._
import at.logic.gapt.utils.{ LogHandler, TimeOutException, withTimeout }

import scala.concurrent.duration.Duration
import scala.io.StdIn
import scala.util.{ Failure, Success, Try }

case class AipOptions( axioms: AxiomFactory = SequentialInductionAxioms(), prover: ResolutionProver = Escargot )

case class ViperOptions(
    verbosity:                Int                      = 2,
    mode:                     String                   = "portfolio",
    fixup:                    Boolean                  = true,
    prooftool:                Boolean                  = false,
    treeGrammarProverOptions: TreeGrammarProverOptions = TreeGrammarProverOptions(),
    aipOptions:               AipOptions               = AipOptions() )
object ViperOptions {
  val usage =
    """Vienna Inductive Prover
      |
      |Usage: viper [common options] [--portfolio|--treegrammar|--analytic [options]] problem.smt2
      |
      |common options:
      |  -v --verbose
      |  -h --help
      |  --prooftool
      |  --fixup --no-fixup
      |
      |--analytic options:
      |  --prover escargot|vampire|prover9|spass|eprover
      |  --axioms sequential|independent|...
      |""".stripMargin

  def parse( args: List[String], opts: ViperOptions ): ( List[String], ViperOptions ) =
    args match {
      case ( "-v" | "--verbose" ) :: rest =>
        parse( rest, opts.copy( verbosity = opts.verbosity + 1 ) )
      case ( "-h" | "--help" ) :: _     => ( Nil, opts.copy( mode = "help" ) )
      case "--prooftool" :: rest        => parse( rest, opts.copy( prooftool = true ) )
      case "--fixup" :: rest            => parse( rest, opts.copy( fixup = true ) )
      case "--no-fixup" :: rest         => parse( rest, opts.copy( fixup = false ) )
      case "--portfolio" :: rest        => parse( rest, opts.copy( mode = "portfolio" ) )
      case "--untrusted_funind" :: rest => parse( rest, opts.copy( mode = "untrusted_funind" ) )
      case "--treegrammar" :: rest =>
        val ( rest_, opts_ ) = parseTreeGrammar( rest, opts.treeGrammarProverOptions )
        parse( rest_, opts.copy( treeGrammarProverOptions = opts_, mode = "treegrammar" ) )
      case "--analytic" :: rest =>
        val ( rest_, opts_ ) = parseAnalytic( rest, opts.aipOptions )
        parse( rest_, opts.copy( aipOptions = opts_, mode = "analytic" ) )
      case _ => ( args, opts )
    }

  def parseAnalytic( args: List[String], opts: AipOptions ): ( List[String], AipOptions ) =
    args match {
      case "--axioms" :: axioms :: rest => parseAnalytic( rest, opts.copy( axioms = axioms match {
        case "sequential"  => SequentialInductionAxioms()
        case "independent" => IndependentInductionAxioms()
        case userDefined   => UserDefinedInductionAxioms( userDefined.split( ";" ).toList )
      } ) )
      case "--prover" :: prover :: rest => parseAnalytic( rest, opts.copy( prover = provers( prover ) ) )
      case _                            => ( args, opts )
    }

  val provers = Map[String, ResolutionProver](
    "prover9" -> Prover9.extendToManySortedViaPredicates,
    "eprover" -> EProver.extendToManySortedViaPredicates,
    "escargot" -> Escargot,
    "iprover" -> IProver.extendToManySortedViaErasure,
    "spass" -> SPASS.extendToManySortedViaPredicates,
    "vampire" -> Vampire.extendToManySortedViaPredicates )

  def parseTreeGrammar( args: List[String], opts: TreeGrammarProverOptions ): ( List[String], TreeGrammarProverOptions ) =
    args match {
      case "--prover" :: prover :: rest => parseTreeGrammar(
        rest,
        opts.copy( instanceProver = provers.getOrElse( prover, throw new IllegalArgumentException( s"unknown prover: $prover" ) ) ) )
      case "--instnum" :: instNum :: rest => parseTreeGrammar( rest, opts.copy( instanceNumber = instNum.toInt ) )
      case "--instsize" :: a :: b :: rest => parseTreeGrammar( rest, opts.copy( instanceSize = a.toFloat -> b.toFloat ) )
      case "--qtys" :: qtys :: rest       => parseTreeGrammar( rest, opts.copy( quantTys = Some( qtys.split( "," ).toSeq.filter( _.nonEmpty ) ) ) )
      case "--gramw" :: w :: rest =>
        val f: InductionGrammar.Production => Int = w match {
          case "scomp" => r => folTermSize( r.lhs ) + folTermSize( r.rhs )
          case "nprods" => _ => 1
        }
        parseTreeGrammar( rest, opts.copy( grammarWeighting = f ) )
      case "--tchknum" :: num :: rest       => parseTreeGrammar( rest, opts.copy( tautCheckNumber = num.toInt ) )
      case "--tchksize" :: a :: b :: rest   => parseTreeGrammar( rest, opts.copy( tautCheckSize = a.toFloat -> b.toFloat ) )
      case "--cansolsize" :: a :: b :: rest => parseTreeGrammar( rest, opts.copy( canSolSize = a.toFloat -> b.toFloat ) )
      case _                                => ( args, opts )
    }
}

object Viper {

  def getStrategies( sequent: HOLSequent, opts: ViperOptions )( implicit ctx: MutableContext ): List[( Duration, Tactical[_] )] =
    opts.mode match {
      case "untrusted_funind" =>
        List( Duration.Inf -> AnalyticInductionTactic( UntrustedFunctionalInductionAxioms, Escargot )
          .aka( "functional induction" ) )
      case "portfolio" =>
        import scala.concurrent.duration._
        val numVars = sequent.succedent match { case Seq( All.Block( xs, _ ) ) => xs.size }
        List(
          10.seconds -> AnalyticInductionTactic( SequentialInductionAxioms(), Escargot ).aka( "analytic sequential" ),
          10.seconds -> AnalyticInductionTactic( IndependentInductionAxioms(), Escargot ).aka( "analytic independent" ) ) ++
          ( 0 until numVars ).toList.map( i => 20.seconds -> introUnivsExcept( i ).andThen(
            new TreeGrammarInductionTactic( opts.treeGrammarProverOptions.copy( quantTys = Some( Seq() ) ) ) ).aka( s"treegrammar without quantifiers $i" ) ) ++
          ( 0 until numVars ).toList.map( i => 60.seconds -> introUnivsExcept( i ).andThen(
            new TreeGrammarInductionTactic( opts.treeGrammarProverOptions ) ).aka( s"treegrammar $i" ) )
      case "treegrammar" => List( Duration.Inf -> new TreeGrammarInductionTactic( opts.treeGrammarProverOptions ).aka( "treegrammar" ) )
      case "analytic" =>
        val axiomsName =
          opts.aipOptions.axioms match {
            case SequentialInductionAxioms( _, _ )  => "sequential"
            case IndependentInductionAxioms( _, _ ) => "independent"
            case UserDefinedInductionAxioms( axs )  => axs.mkString( ";" )
          }
        List( Duration.Inf -> AnalyticInductionTactic( opts.aipOptions.axioms, opts.aipOptions.prover ).
          aka( s"analytic $axiomsName" ) )
    }

  private def timeit[T]( f: => T ): ( T, Duration ) = {
    val a = System.currentTimeMillis()
    val res = f
    val b = System.currentTimeMillis()
    import scala.concurrent.duration._
    ( res, ( b - a ).milliseconds )
  }

  def apply( problem: TipProblem ): Option[LKProof] =
    apply( problem.toSequent )( problem.ctx.newMutable )

  def apply( problem: TipProblem, verbosity: Int ): Option[LKProof] =
    apply( problem, ViperOptions( verbosity = verbosity ) )

  def apply( problem: TipProblem, options: ViperOptions ): Option[LKProof] =
    apply( problem.toSequent, options )( problem.ctx.newMutable )

  def apply( sequent: HOLSequent )( implicit ctx: MutableContext ): Option[LKProof] =
    apply( sequent, ViperOptions( verbosity = 3 ) )

  def apply( sequent: HOLSequent, opts: ViperOptions )( implicit ctx: MutableContext ): Option[LKProof] =
    apply( sequent, opts.verbosity, getStrategies( sequent, opts ) )

  def apply( sequent: HOLSequent, verbosity: Int,
             strategies: List[( Duration, Tactical[_] )] )(
    implicit
    ctx: MutableContext ): Option[LKProof] = LogHandler.scope {
    if ( verbosity >= 3 ) LogHandler.current.value = LogHandler.verbose

    if ( verbosity >= 2 ) println( sequent.toSigRelativeString )

    val state0 = ProofState( sequent )
    strategies.view.flatMap {
      case ( duration, strategy ) =>
        if ( verbosity >= 2 ) println( s"trying $strategy" )
        timeit( Try( withTimeout( duration ) { strategy.andThen( now )( state0 ) } ) ) match {
          case ( Success( Right( ( _, state_ ) ) ), time ) =>
            if ( verbosity >= 1 ) println( s"$strategy successful after $time" )
            Some( state_.result )
          case ( Failure( _: TimeOutException ), time ) =>
            if ( verbosity >= 1 ) println( s"$strategy timed out after $time" )
            None
          case ( failure, time ) =>
            if ( verbosity >= 1 ) println( s"$strategy failed after $time" )
            if ( verbosity >= 2 )
              ( failure: @unchecked ) match {
                case Failure( ex ) =>
                  ex.printStackTrace()
                case Success( Left( tacticalFailure ) ) =>
                  println( tacticalFailure )
              }
            None
        }
    }.headOption
  }

  def main( args: Array[String] ): Unit = {
    val ( fileNames, opts ) = ViperOptions.parse( args.toList, ViperOptions( fixup = TipSmtParser.isInstalled ) )
    val files = fileNames.map {
      case "-" => StringInputFile( Stream.continually( StdIn.readLine() ).takeWhile( _ != null ).mkString )
      case fn  => InputFile.fromPath( FilePath( fn ) )
    }

    if ( opts.mode == "help" || files.size != 1 ) return print( ViperOptions.usage )
    val file = files.head

    val problem = if ( opts.fixup ) TipSmtParser.fixupAndParse( file ) else TipSmtParser.parse( file )
    implicit val ctx: MutableContext = problem.ctx.newMutable

    apply( problem.toSequent, opts ) match {
      case Some( proof ) =>
        ctx check proof
        require( proof.conclusion isSubsetOf problem.toSequent )
        println( "proof found" )
        if ( opts.prooftool ) prooftool( proof )
      case None =>
        println( "could not solve problem" )
        sys.exit( 1 )
    }
  }

}
