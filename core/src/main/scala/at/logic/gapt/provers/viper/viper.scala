package at.logic.gapt.provers.viper

import ammonite.ops._
import at.logic.gapt.expr.{ All, Formula }
import at.logic.gapt.expr.fol.folTermSize
import at.logic.gapt.formats.tip.{ TipProblem, TipSmtParser }
import at.logic.gapt.formats.{ InputFile, StringInputFile }
import at.logic.gapt.grammars.Rule
import at.logic.gapt.grammars.induction2.InductionGrammar
import at.logic.gapt.proofs.{ Context, HOLSequent, MutableContext, withSection }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.gaptic.tactics.AnalyticInductionTactic
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.prooftool.prooftool
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.viper.aip.axioms._
import at.logic.gapt.provers.viper.grammars.TreeGrammarProverOptions.SmtEquationMode
import at.logic.gapt.provers.{ Prover, ResolutionProver }
import at.logic.gapt.provers.viper.grammars._
import at.logic.gapt.utils.{ Logger, TimeOutException, withTimeout }
import org.apache.commons.lang3.exception.ExceptionUtils

import scala.concurrent.duration.Duration
import scala.io.StdIn
import scala.util.{ Failure, Success, Try }

class TreeGrammarInductionTactic( options: TreeGrammarProverOptions = TreeGrammarProverOptions() )( implicit ctx: Context ) extends at.logic.gapt.proofs.gaptic.Tactic[Unit] {
  import at.logic.gapt.proofs.gaptic._

  def copy( options: TreeGrammarProverOptions ) = new TreeGrammarInductionTactic( options )

  def verbose: TreeGrammarInductionTactic = {
    Logger.makeVerbose( classOf[TreeGrammarProver] )
    this
  }

  def instanceNumber( n: Int ) = copy( options.copy( instanceNumber = n ) )
  def instanceSize( from: Float, to: Float ) = copy( options.copy( instanceSize = ( from, to ) ) )
  def instanceProver( prover: Prover ) = copy( options.copy( instanceProver = prover ) )
  def smtSolver( prover: Prover ) = copy( options.copy( smtSolver = prover ) )
  def smtEquationMode( mode: SmtEquationMode ) = copy( options.copy( smtEquationMode = mode ) )
  def findingMethod( method: String ) = copy( options.copy( findingMethod = "maxsat" ) )
  def quantTys( tys: String* ) = copy( options.copy( quantTys = Some( tys ) ) )
  def grammarWeighting( w: Rule => Int ) = copy( options.copy( grammarWeighting = w ) )
  def tautCheckNumber( n: Int ) = copy( options.copy( tautCheckNumber = n ) )
  def tautCheckSize( from: Float, to: Float ) = copy( options.copy( tautCheckSize = ( from, to ) ) )
  def canSolSize( from: Float, to: Float ) = copy( options.copy( canSolSize = ( from, to ) ) )
  def canSolSize( size: Int ) = copy( options.copy( canSolSize = ( size, size ) ) )
  def doForgetOne( enable: Boolean = true ) = copy( options.copy( forgetOne = enable ) )
  def equationalTheory( equations: Formula* ) = copy( options.copy( equationalTheory = equations ) )

  override def apply( goal: OpenAssumption ): Either[TacticalFailure, ( Unit, LKProof )] = {
    implicit val ctx2: MutableContext = ctx.newMutable
    withSection { section =>
      val groundGoal = section.groundSequent( goal.conclusion )
      val viper = new TreeGrammarProver( ctx2, groundGoal, options )
      try {
        Right( () -> viper.solve() )
      } catch {
        case t: TimeOutException => throw t
        case t: ThreadDeath      => throw t
        case t: Throwable =>
          Left( TacticalFailure( this, ExceptionUtils.getStackTrace( t ) ) )
      }
    }
  }

  override def toString = "treeGrammarProver"
}

class TreeGrammarInductionTactic2( options: grammars2.TreeGrammarProverOptions = grammars2.TreeGrammarProverOptions() )( implicit ctx: Context ) extends at.logic.gapt.proofs.gaptic.Tactic[Unit] {
  import at.logic.gapt.proofs.gaptic._

  def copy( options: grammars2.TreeGrammarProverOptions ) = new TreeGrammarInductionTactic2( options )

  def verbose: TreeGrammarInductionTactic2 = {
    Logger.makeVerbose( classOf[grammars2.TreeGrammarProver] )
    this
  }

  def instanceNumber( n: Int ) = copy( options.copy( instanceNumber = n ) )
  def instanceSize( from: Float, to: Float ) = copy( options.copy( instanceSize = ( from, to ) ) )
  def instanceProver( prover: Prover ) = copy( options.copy( instanceProver = prover ) )
  def smtSolver( prover: Prover ) = copy( options.copy( smtSolver = prover ) )
  def smtEquationMode( mode: grammars2.TreeGrammarProverOptions.SmtEquationMode ) = copy( options.copy( smtEquationMode = mode ) )
  def quantTys( tys: String* ) = copy( options.copy( quantTys = Some( tys ) ) )
  def grammarWeighting( w: InductionGrammar.Production => Int ) = copy( options.copy( grammarWeighting = w ) )
  def tautCheckNumber( n: Int ) = copy( options.copy( tautCheckNumber = n ) )
  def tautCheckSize( from: Float, to: Float ) = copy( options.copy( tautCheckSize = ( from, to ) ) )
  def canSolSize( from: Float, to: Float ) = copy( options.copy( canSolSize = ( from, to ) ) )
  def canSolSize( size: Int ) = copy( options.copy( canSolSize = ( size, size ) ) )
  def equationalTheory( equations: Formula* ) = copy( options.copy( equationalTheory = equations ) )

  override def apply( goal: OpenAssumption ): Either[TacticalFailure, ( Unit, LKProof )] = {
    implicit val ctx2: MutableContext = ctx.newMutable
    withSection { section =>
      val groundGoal = section.groundSequent( goal.conclusion )
      val viper = new grammars2.TreeGrammarProver( ctx2, groundGoal, options )
      try {
        Right( () -> viper.solve() )
      } catch {
        case t: TimeOutException => throw t
        case t: ThreadDeath      => throw t
        case t: Throwable =>
          Left( TacticalFailure( this, ExceptionUtils.getStackTrace( t ) ) )
      }
    }
  }

  override def toString = "treeGrammarProver"
}

case class AipOptions( axioms: AxiomFactory = SequentialInductionAxioms(), prover: ResolutionProver = Escargot )

case class ViperOptions(
    verbosity:                 Int                                = 2,
    mode:                      String                             = "portfolio",
    fixup:                     Boolean                            = true,
    prooftool:                 Boolean                            = false,
    firstOrderProver:          ResolutionProver                   = Escargot,
    treeGrammarProverOptions:  TreeGrammarProverOptions           = TreeGrammarProverOptions(),
    treeGrammarProverOptions2: grammars2.TreeGrammarProverOptions = grammars2.TreeGrammarProverOptions(),
    aipOptions:                AipOptions                         = AipOptions() )
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
      case "--treegrammar2" :: rest =>
        val ( rest_, opts_ ) = parseTreeGrammar2( rest, opts.treeGrammarProverOptions2 )
        parse( rest_, opts.copy( treeGrammarProverOptions2 = opts_, mode = "treegrammar2" ) )
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
      "iprover" -> iprover,
      "spass" -> spass,
      "vampire" -> vampire )
  }

  def parseTreeGrammar( args: List[String], opts: TreeGrammarProverOptions ): ( List[String], TreeGrammarProverOptions ) =
    args match {
      case "--prover" :: prover :: rest => parseTreeGrammar(
        rest,
        opts.copy( instanceProver = provers.getOrElse( prover, throw new IllegalArgumentException( s"unknown prover: $prover" ) ) ) )
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

  def parseTreeGrammar2( args: List[String], opts: grammars2.TreeGrammarProverOptions ): ( List[String], grammars2.TreeGrammarProverOptions ) =
    args match {
      case "--prover" :: prover :: rest => parseTreeGrammar2(
        rest,
        opts.copy( instanceProver = provers.getOrElse( prover, throw new IllegalArgumentException( s"unknown prover: $prover" ) ) ) )
      case "--instnum" :: instNum :: rest => parseTreeGrammar2( rest, opts.copy( instanceNumber = instNum.toInt ) )
      case "--instsize" :: a :: b :: rest => parseTreeGrammar2( rest, opts.copy( instanceSize = a.toFloat -> b.toFloat ) )
      case "--qtys" :: qtys :: rest       => parseTreeGrammar2( rest, opts.copy( quantTys = Some( qtys.split( "," ).toSeq.filter( _.nonEmpty ) ) ) )
      case "--gramw" :: w :: rest =>
        val f: InductionGrammar.Production => Int = w match {
          case "scomp" => r => folTermSize( r.lhs ) + folTermSize( r.rhs )
          case "nprods" => _ => 1
        }
        parseTreeGrammar2( rest, opts.copy( grammarWeighting = f ) )
      case "--tchknum" :: num :: rest       => parseTreeGrammar2( rest, opts.copy( tautCheckNumber = num.toInt ) )
      case "--tchksize" :: a :: b :: rest   => parseTreeGrammar2( rest, opts.copy( tautCheckSize = a.toFloat -> b.toFloat ) )
      case "--cansolsize" :: a :: b :: rest => parseTreeGrammar2( rest, opts.copy( canSolSize = a.toFloat -> b.toFloat ) )
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
        ( List(
          10.seconds -> AnalyticInductionTactic( IndependentInductionAxioms(), Escargot ).aka( "analytic independent" ),
          10.seconds -> AnalyticInductionTactic( SequentialInductionAxioms(), Escargot ).aka( "analytic sequential" ),
          20.seconds -> new TreeGrammarInductionTactic( opts.treeGrammarProverOptions.copy( quantTys = Some( Seq() ) ) ).aka( "treegrammar without quantifiers" ),
          60.seconds -> new TreeGrammarInductionTactic( opts.treeGrammarProverOptions ).aka( "treegrammar" ) ) ++
          ( for ( i <- 0 until numVars ) yield 20.seconds -> introUnivsExcept( i ).andThen( new TreeGrammarInductionTactic( opts.treeGrammarProverOptions ).aka( "treegrammar " ) ) ) ++
          ( 0 until numVars ).flatMap( i => List(
            20.seconds -> introUnivsExcept( i ).andThen( new TreeGrammarInductionTactic2( opts.treeGrammarProverOptions2.copy( quantTys = Some( Seq() ) ) ) ).aka( s"treegrammar2 without quantifiers $i" ),
            60.seconds -> introUnivsExcept( i ).andThen( new TreeGrammarInductionTactic2( opts.treeGrammarProverOptions2 ) ).aka( s"treegrammar2 $i" ) ) ) ).reverse
      case "treegrammar"  => List( Duration.Inf -> new TreeGrammarInductionTactic( opts.treeGrammarProverOptions ).aka( "treegrammar" ) )
      case "treegrammar2" => List( Duration.Inf -> new TreeGrammarInductionTactic2( opts.treeGrammarProverOptions2 ).aka( "treegrammar2" ) )
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
             strategies: List[( Duration, Tactical[_] )] )( implicit ctx: MutableContext ): Option[LKProof] = {
    if ( verbosity >= 3 ) Logger.makeVerbose( classOf[TreeGrammarProver] )
    if ( verbosity >= 3 ) Logger.makeVerbose( classOf[grammars2.TreeGrammarProver] )
    if ( verbosity >= 4 ) Escargot.makeVerbose()

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

    Logger.setConsolePattern( "%message%n" )

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
