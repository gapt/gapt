package at.logic.gapt.provers.viper

import ammonite.ops._
import at.logic.gapt.expr.fol.folTermSize
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.formats.{ InputFile, StringInputFile }
import at.logic.gapt.grammars.Rule
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.gaptic.tactics.AnalyticInductionTactic
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.prooftool.prooftool
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.viper.aip.axioms.{ AxiomFactory, IndependentInductionAxioms, SequentialInductionAxioms, UserDefinedInductionAxioms }
import at.logic.gapt.provers.{ Prover, ResolutionProver }
import at.logic.gapt.provers.viper.grammars._
import at.logic.gapt.utils.{ Logger, TimeOutException, withTimeout }
import org.apache.commons.lang3.exception.ExceptionUtils

import scala.concurrent.duration.Duration
import scala.io.StdIn
import scala.util.{ Failure, Success, Try }

class ViperTactic( options: TreeGrammarProverOptions = TreeGrammarProverOptions() )( implicit ctx: Context ) extends at.logic.gapt.proofs.gaptic.Tactic[Unit] {
  import at.logic.gapt.proofs.gaptic._

  def copy( options: TreeGrammarProverOptions ) = new ViperTactic( options )

  def instanceNumber( n: Int ) = copy( options.copy( instanceNumber = n ) )
  def instanceSize( from: Float, to: Float ) = copy( options.copy( instanceSize = ( from, to ) ) )
  def instanceProver( prover: Prover ) = copy( options.copy( instanceProver = prover ) )
  def findingMethod( method: String ) = copy( options.copy( findingMethod = "maxsat" ) )
  def quantTys( tys: String* ) = copy( options.copy( quantTys = Some( tys ) ) )
  def grammarWeighting( w: Rule => Int ) = copy( options.copy( grammarWeighting = w ) )
  def tautCheckNumber( n: Int ) = copy( options.copy( tautCheckNumber = n ) )
  def tautCheckSize( from: Float, to: Float ) = copy( options.copy( tautCheckSize = ( from, to ) ) )
  def canSolSize( from: Float, to: Float ) = copy( options.copy( canSolSize = ( from, to ) ) )
  def doForgetOne( enable: Boolean = true ) = copy( options.copy( forgetOne = enable ) )

  override def apply( goal: OpenAssumption ): Either[TacticalFailure, ( Unit, LKProof )] = {
    val viper = new TreeGrammarProver( ctx, goal.conclusion, options )
    try {
      Right( () -> viper.solve() )
    } catch {
      case t: Throwable =>
        Left( TacticalFailure( this, ExceptionUtils.getStackTrace( t ) ) )
    }
  }

  override def toString = options.toString
}

case class AipOptions( axioms: AxiomFactory = SequentialInductionAxioms(), prover: ResolutionProver = Escargot )

case class ViperOptions(
  verbosity:                Int                      = 0,
  mode:                     String                   = "portfolio",
  fixup:                    Boolean                  = true,
  prooftool:                Boolean                  = false,
  firstOrderProver:         ResolutionProver         = Escargot,
  treeGrammarProverOptions: TreeGrammarProverOptions = TreeGrammarProverOptions(),
  aipOptions:               AipOptions               = AipOptions()
)
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
      case ( "-h" | "--help" ) :: _ => ( Nil, opts.copy( mode = "help" ) )
      case "--prooftool" :: rest    => parse( rest, opts.copy( prooftool = true ) )
      case "--fixup" :: rest        => parse( rest, opts.copy( fixup = true ) )
      case "--no-fixup" :: rest     => parse( rest, opts.copy( fixup = false ) )
      case "--portfolio" :: rest    => parse( rest, opts.copy( mode = "portfolio" ) )
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

  val provers = {
    import at.logic.gapt.provers.viper.aip.provers._
    Map[String, ResolutionProver](
      "prover9" -> prover9,
      "eprover" -> eprover,
      "escargot" -> Escargot,
      "spass" -> spass,
      "vampire" -> vampire
    )
  }

  def parseTreeGrammar( args: List[String], opts: TreeGrammarProverOptions ): ( List[String], TreeGrammarProverOptions ) =
    args match {
      case "--prover" :: prover :: rest => parseTreeGrammar(
        rest,
        opts.copy( instanceProver = provers.getOrElse( prover, throw new IllegalArgumentException( s"unknown prover: $prover" ) ) )
      )
      case "--instnum" :: instNum :: rest => parseTreeGrammar( rest, opts.copy( instanceNumber = instNum.toInt ) )
      case "--instsize" :: a :: b :: rest => parseTreeGrammar( rest, opts.copy( instanceSize = a.toFloat -> b.toFloat ) )
      case "--findmth" :: mth :: rest     => parseTreeGrammar( rest, opts.copy( findingMethod = mth ) )
      case "--qtys" :: qtys :: rest       => parseTreeGrammar( rest, opts.copy( quantTys = Some( qtys.split( "," ).toSeq.filter( _.nonEmpty ) ) ) )
      case "--gramw" :: w :: rest =>
        val f: Rule => Int = w match {
          case "scomp" => r => folTermSize( r.lhs ) + folTermSize( r.rhs )
          case "nprods" => _ => 1
        }
        parseTreeGrammar( rest, opts.copy( grammarWeighting = f ) )
      case "--tchknum" :: num :: rest       => parseTreeGrammar( rest, opts.copy( tautCheckNumber = num.toInt ) )
      case "--tchksize" :: a :: b :: rest   => parseTreeGrammar( rest, opts.copy( tautCheckSize = a.toFloat -> b.toFloat ) )
      case "--cansolsize" :: a :: b :: rest => parseTreeGrammar( rest, opts.copy( canSolSize = a.toFloat -> b.toFloat ) )
      case "--forgetone" :: rest            => parseTreeGrammar( rest, opts.copy( forgetOne = true ) )
      case "--no-forgetone" :: rest         => parseTreeGrammar( rest, opts.copy( forgetOne = false ) )
      case _                                => ( args, opts )
    }
}

object Viper {

  val optionRegex = """;\s*viper\s+(.*)""".r
  def extractOptions( tipSmtCode: InputFile ): List[String] =
    tipSmtCode.read.split( "\n" ).view.flatMap {
      case optionRegex( args ) => args.split( """\s+""" ).
        map { a => if ( a.startsWith( "\"" ) ) a.substring( 1, a.length - 1 ) else a }
      case _ => Seq()
    }.toList

  def getStrategies( opts: ViperOptions )( implicit ctx: Context ): List[( Duration, Tactical[_] )] =
    opts.mode match {
      case "portfolio" =>
        import scala.concurrent.duration._
        List(
          10.seconds -> AnalyticInductionTactic( IndependentInductionAxioms(), Escargot ).aka( "analytic independent" ),
          10.seconds -> AnalyticInductionTactic( SequentialInductionAxioms(), Escargot ).aka( "analytic sequential" ),
          20.seconds -> new ViperTactic( opts.treeGrammarProverOptions.copy( quantTys = Some( Seq() ) ) ).aka( "treegrammar without quantifiers" ),
          60.seconds -> new ViperTactic( opts.treeGrammarProverOptions ).aka( "treegrammar" )
        )
      case "treegrammar" => List( Duration.Inf -> new ViperTactic( opts.treeGrammarProverOptions ).aka( "treegrammar" ) )
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

  def timeit[T]( f: => T ): ( T, Duration ) = {
    val a = System.currentTimeMillis()
    val res = f
    val b = System.currentTimeMillis()
    import scala.concurrent.duration._
    ( res, ( b - a ).milliseconds )
  }

  def main( args: Array[String] ): Unit = {
    val ( fileNames, opts0 ) = ViperOptions.parse( args.toList, ViperOptions( fixup = TipSmtParser.isInstalled ) )
    val hasCmdLineOpts = fileNames.size != args.length
    val files = fileNames.map {
      case "-" => StringInputFile( Stream.continually( StdIn.readLine() ).takeWhile( _ != null ).mkString )
      case fn  => InputFile.fromPath( FilePath( fn ) )
    }

    if ( opts0.mode == "help" || files.size != 1 ) return print( ViperOptions.usage )
    val file = files.head

    Logger.setConsolePattern( "%message%n" )
    if ( opts0.verbosity >= 2 ) Logger.makeVerbose( classOf[TreeGrammarProver] )

    val opts = if ( hasCmdLineOpts ) opts0 else ViperOptions.parse( extractOptions( file ), opts0 )._2
    val problem = if ( opts.fixup ) TipSmtParser.fixupAndParse( file ) else TipSmtParser.parse( file )
    implicit val ctx = problem.ctx

    if ( opts0.verbosity >= 1 ) println( problem.toSequent.toSigRelativeString )

    val state0 = ProofState( problem.toSequent )
    getStrategies( opts ).view.flatMap {
      case ( duration, strategy ) =>
        if ( opts0.verbosity >= 1 ) println( s"trying $strategy" )
        timeit( Try( withTimeout( duration ) { strategy.andThen( now )( state0 ) } ) ) match {
          case ( Success( Right( ( _, state_ ) ) ), time ) =>
            println( s"$strategy successful after $time" )
            Some( state_.result )
          case ( failure, time ) =>
            println( s"$strategy failed after $time" )
            if ( opts0.verbosity >= 1 )
              ( failure: @unchecked ) match {
                case Failure( _: TimeOutException )     => println( "(due to timeout)" )
                case Failure( ex )                      => ex.printStackTrace()
                case Success( Left( tacticalFailure ) ) => println( tacticalFailure )
              }
            None
        }
    }.headOption match {
      case Some( proof ) =>
        if ( false ) { // this doesn't work with Skolem inferences atm
          ctx check proof
          require( proof.conclusion isSubsetOf problem.toSequent )
        }
        println( "proof found" )
        if ( opts0.prooftool ) prooftool( proof )
      case None =>
        println( "could not solve problem" )
        sys.exit( 1 )
    }
  }

}
