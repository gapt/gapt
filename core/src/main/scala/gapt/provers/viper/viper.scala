package gapt.provers.viper

import ammonite.ops._
import gapt.expr.formula.All
import gapt.expr.formula.Formula
import gapt.expr.formula.fol.folTermSize
import gapt.expr.formula.hol.containsQuantifierOnLogicalLevel
import gapt.expr.ty.TBase
import gapt.expr.util.freeVariables
import gapt.formats.InputFile
import gapt.formats.StdinInputFile
import gapt.formats.tip.TipProblem
import gapt.formats.tip.TipSmtImporter
import gapt.grammars.InductionGrammar
import gapt.proofs.HOLSequent
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.gaptic._
import gapt.proofs.gaptic.tactics.{ AnalyticInductionTactic, SuperpositionInductionTactic }
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.macros.ContractionMacroRule
import gapt.proofs.lk.rules.macros.ForallRightBlock
import gapt.proofs.lk.rules.macros.OrRightMacroRule
import gapt.proofs.resolution.ResolutionToLKProof
import gapt.proofs.resolution.structuralCNF
import gapt.prooftool.prooftool
import gapt.provers.ResolutionProver
import gapt.provers.eprover.EProver
import gapt.provers.escargot.Escargot
import gapt.provers.iprover.IProver
import gapt.provers.prover9.Prover9
import gapt.provers.spass.SPASS
import gapt.provers.vampire.Vampire
import gapt.provers.viper.aip.axioms._
import gapt.provers.viper.grammars._
import gapt.provers.viper.spin.SpinOptions
import gapt.utils.LogHandler
import gapt.utils.TimeOutException
import gapt.utils.withTimeout

import scala.concurrent.duration.Duration
import scala.util.Failure
import scala.util.Success
import scala.util.Try

case class AipOptions( axioms: AxiomFactory = SequentialInductionAxioms(), prover: ResolutionProver = Escargot )

case class ViperOptions(
    verbosity:                Int                      = 2,
    mode:                     String                   = "portfolio",
    fixup:                    Boolean                  = true,
    prooftool:                Boolean                  = false,
    treeGrammarProverOptions: TreeGrammarProverOptions = TreeGrammarProverOptions(),
    aipOptions:               AipOptions               = AipOptions(),
    spinOptions:              SpinOptions              = SpinOptions(),
    tipProblem:               Option[TipProblem]       = None )
object ViperOptions {
  val usage =
    """Vienna Inductive Prover
      |
      |Usage: viper [common options] [--portfolio|--treegrammar|--analytic [options]|--spin [options]] problem.smt2
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
      |
      |--spin options:
      |  --generalization true|false
      |  --testing        true|false|1|2|...
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
      case "--spin" :: rest =>
        val ( rest_, opts_ ) = parseSpin( rest, opts.spinOptions )
        parse( rest_, opts.copy( spinOptions = opts_, mode = "spin" ) )
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

  def parseSpin( args: List[String], opts: SpinOptions ): ( List[String], SpinOptions ) =
    args match {
      case "--generalization" :: toggle :: rest => parseSpin( rest, opts.copy( performGeneralization = toggle match {
        case "true"  => true
        case "false" => false
      } ) )
      case "--testing" :: toggle :: rest => parseSpin( rest, opts.copy( sampleTestTerms = toggle match {
        case "true"                     => SpinOptions().sampleTestTerms
        case "false"                    => 0
        case d if d.forall( _.isDigit ) => d.toInt
      } ) )
      case _ => ( args, opts )
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
      case "--onquant" :: i :: rest => parseTreeGrammar( rest, opts.copy( goalQuantifier = i.toInt ) )
      case "--prover" :: prover :: rest => parseTreeGrammar(
        rest,
        opts.copy( instanceProver = provers.getOrElse(
          prover,
          throw new IllegalArgumentException( s"unknown prover: $prover" ) ) ) )
      case "--instnum" :: instNum :: rest => parseTreeGrammar( rest, opts.copy( instanceNumber = instNum.toInt ) )
      case "--instsize" :: a :: b :: rest => parseTreeGrammar( rest, opts.copy( instanceSize = a.toFloat -> b.toFloat ) )
      case "--qtys" :: qtys :: rest => parseTreeGrammar(
        rest,
        opts.copy( quantTys = Some( qtys.split( "," ).toSeq.filter( _.nonEmpty ).map( TBase( _ ) ) ) ) )
      case "--gramw" :: w :: rest =>
        val f: InductionGrammar.Production => Int = w match {
          case "scomp" => r => folTermSize( r.lhs ) + folTermSize( r.rhs )
          case "nprods" => _ => 1
        }
        parseTreeGrammar( rest, opts.copy( grammarWeighting = f ) )
      case "--tchknum" :: num :: rest => parseTreeGrammar( rest, opts.copy( tautCheckNumber = num.toInt ) )
      case "--tchksize" :: a :: b :: rest => parseTreeGrammar(
        rest,
        opts.copy( tautCheckSize = a.toFloat -> b.toFloat ) )
      case "--cansolsize" :: a :: b :: rest => parseTreeGrammar( rest, opts.copy( canSolSize = a.toFloat -> b.toFloat ) )
      case "--interp" :: rest               => parseTreeGrammar( rest, opts.copy( bupSolver = InductionBupSolver.Interpolation ) )
      case _                                => ( args, opts )
    }
}

object Viper {

  def getStrategies( sequent: HOLSequent, opts: ViperOptions )( implicit ctx: MutableContext ): List[( Duration, Tactic[_] )] =
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
            new TreeGrammarInductionTactic( opts.treeGrammarProverOptions.copy( quantTys = Some( Seq() ) ) ) )
            .aka( s"treegrammar without quantifiers $i" ) ) ++
          ( 0 until numVars ).toList.map( i => 60.seconds -> introUnivsExcept( i ).andThen(
            new TreeGrammarInductionTactic( opts.treeGrammarProverOptions ) ).aka( s"treegrammar $i" ) )
      case "treegrammar" =>
        List( Duration.Inf ->
          introUnivsExcept( opts.treeGrammarProverOptions.goalQuantifier ).
          andThen( new TreeGrammarInductionTactic( opts.treeGrammarProverOptions ) ).
          aka( "treegrammar" ) )
      case "analytic" =>
        val axiomsName =
          opts.aipOptions.axioms match {
            case SequentialInductionAxioms( _, _ )  => "sequential"
            case IndependentInductionAxioms( _, _ ) => "independent"
            case UserDefinedInductionAxioms( axs )  => axs.mkString( ";" )
          }
        List( Duration.Inf -> AnalyticInductionTactic( opts.aipOptions.axioms, opts.aipOptions.prover ).
          aka( s"analytic $axiomsName" ) )
      case "spin" =>
        if ( opts.tipProblem.isEmpty )
          throw new IllegalStateException( "No TipProblem given." )

        val generalize = opts.spinOptions.performGeneralization
        val testTerms = opts.spinOptions.sampleTestTerms
        List( Duration.Inf -> SuperpositionInductionTactic( opts.spinOptions )
          .aka( s"spin (generalization = $generalize, test terms = $testTerms)" ) )
    }

  private def timeit[T]( f: => T ): ( T, Duration ) = {
    val a = System.currentTimeMillis()
    val res = f
    val b = System.currentTimeMillis()
    import scala.concurrent.duration._
    ( res, ( b - a ).milliseconds )
  }

  def clausifyIfNotPrenex( implicit ctx: MutableContext ): Tactic[Unit] = Tactic {
    import gapt.proofs.gaptic._
    def isPrenexPi1( f: Formula ): Boolean =
      f match { case All.Block( _, g ) => !containsQuantifierOnLogicalLevel( g ) }
    currentGoal.flatMap {
      case goal if goal.endSequent.antecedent.forall( isPrenexPi1 ) =>
        skip
      case goal =>
        val cnf = structuralCNF( goal.endSequent.copy( succedent = Vector() ) )
        val cnfPs = cnf.map { cls =>
          var p = ResolutionToLKProof.withDefs( cls )
          for ( a <- cls.conclusion.antecedent ) p = NegRightRule( p, a )
          p = OrRightMacroRule( p, cls.conclusion.map( -_, identity ).elements )
          val fvs = freeVariables( p.endSequent.succedent.head ).toSeq
          p = ForallRightBlock( p, All.Block( fvs, p.endSequent.succedent.head ), fvs )
          p
        }
        val newGoal = OpenAssumption( goal.labelledSequent.copy( antecedent =
          for ( ( p, i ) <- cnfPs.toVector.zipWithIndex ) yield s"h_$i" -> p.endSequent.succedent.head ) )
        insert( cnfPs.foldLeft[LKProof]( newGoal )( ( q, cnfP ) =>
          if ( !q.endSequent.antecedent.contains( cnfP.endSequent.succedent.head ) ) q else
            ContractionMacroRule( CutRule( cnfP, q, cnfP.endSequent.succedent.head ) ) ) )
    }
  }

  def apply( problem: TipProblem ): Option[LKProof] =
    apply( problem.toSequent, ViperOptions( tipProblem = Some( problem ) ) )( problem.context.newMutable )

  def apply( problem: TipProblem, verbosity: Int ): Option[LKProof] =
    apply( problem, ViperOptions( verbosity = verbosity, tipProblem = Some( problem ) ) )

  def apply( problem: TipProblem, options: ViperOptions ): Option[LKProof] =
    apply( problem.toSequent, options.copy( tipProblem = Some( problem ) ) )( problem.context.newMutable )

  def apply( sequent: HOLSequent )( implicit ctx: MutableContext ): Option[LKProof] =
    apply( sequent, ViperOptions( verbosity = 3 ) )

  def apply( sequent: HOLSequent, opts: ViperOptions )( implicit ctx: MutableContext ): Option[LKProof] =
    apply( sequent, opts.verbosity, getStrategies( sequent, opts ) )

  def apply( sequent: HOLSequent, verbosity: Int,
             strategies: List[( Duration, Tactic[_] )] )(
    implicit
    ctx: MutableContext ): Option[LKProof] = LogHandler.scope {
    LogHandler.verbosity.value = LogHandler.verbosity.value.increase( math.max( 0, verbosity - 2 ) )

    if ( verbosity >= 2 ) println( sequent.toSigRelativeString )

    val state0 = ProofState( sequent ) + clausifyIfNotPrenex
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
    val ( fileNames, opts ) = ViperOptions.parse( args.toList, ViperOptions( fixup = TipSmtImporter.isInstalled ) )
    val files = fileNames.map {
      case "-" => StdinInputFile()
      case fn  => InputFile.fromPath( FilePath( fn ) )
    }

    if ( opts.mode == "help" || files.size != 1 ) return print( ViperOptions.usage )
    val file = files.head

    val problem = if ( opts.fixup ) TipSmtImporter.fixupAndLoad( file ) else TipSmtImporter.load( file )
    implicit val ctx: MutableContext = problem.context.newMutable

    apply( problem.toSequent, opts.copy( tipProblem = Some( problem ) ) ) match {
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
