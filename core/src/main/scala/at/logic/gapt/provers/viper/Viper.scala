package at.logic.gapt.provers.viper

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.{ folSubTerms, folTermSize }
import at.logic.gapt.expr.hol.{ CNFp, instantiate }
import at.logic.gapt.formats.{ InputFile, StringInputFile }
import at.logic.gapt.formats.tip.{ TipProblem, TipSmtParser }
import at.logic.gapt.grammars.{ RecursionScheme, Rule, instantiateRS }
import at.logic.gapt.proofs.Context.{ BaseTypes, StructurallyInductiveTypes }
import at.logic.gapt.proofs.{ Context, HOLSequent, Sequent }
import at.logic.gapt.proofs.expansion.{ ExpansionProof, InstanceTermEncoding, extractInstances }
import at.logic.gapt.proofs.lk.{ EquationalLKProver, LKProof, skolemize }
import at.logic.gapt.proofs.reduction._
import at.logic.gapt.prooftool.prooftool
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.spass.SPASS
import at.logic.gapt.provers.verit.VeriT
import at.logic.gapt.provers.viper.ViperOptions.FloatRange
import at.logic.gapt.utils.Logger

import scala.collection.mutable
import scala.io.StdIn
import ammonite.ops._

case class ViperOptions(
  instanceNumber:   Int                 = 10,
  instanceSize:     FloatRange          = ( 0, 2 ),
  instanceProver:   String              = "escargot",
  findingMethod:    String              = "maxsat",
  quantTys:         Option[Seq[String]] = None,
  grammarWeighting: Rule => Int         = _ => 1,
  tautCheckNumber:  Int                 = 10,
  tautCheckSize:    FloatRange          = ( 2, 3 ),
  canSolSize:       FloatRange          = ( 2, 4 ),
  forgetOne:        Boolean             = false,
  prooftool:        Boolean             = false,
  fixup:            Boolean             = false
)
object ViperOptions {
  type FloatRange = ( Float, Float )

  private def parseRange( ran: String ): FloatRange = {
    val Seq( from, to ) = ran.split( "," ).toSeq
    from.toFloat -> to.toFloat
  }

  private def parseAndApply( k: String, v: String, opts: ViperOptions ): ViperOptions = k match {
    case "instnum"    => opts.copy( instanceNumber = v.toInt )
    case "instsize"   => opts.copy( instanceSize = parseRange( v ) )
    case "instprover" => opts.copy( instanceProver = v )
    case "findmth"    => opts.copy( findingMethod = v )
    case "qtys"       => opts.copy( quantTys = Some( v.split( "," ).toSeq.filter( _.nonEmpty ) ) )
    case "gramw" => v match {
      case "scomp"  => opts.copy( grammarWeighting = r => folTermSize( r.lhs ) + folTermSize( r.rhs ) )
      case "nprods" => opts.copy( grammarWeighting = _ => 1 )
    }
    case "tchknum"    => opts.copy( tautCheckNumber = v.toInt )
    case "tchksize"   => opts.copy( tautCheckSize = parseRange( v ) )
    case "cansolsize" => opts.copy( canSolSize = parseRange( v ) )
    case "forgetone"  => opts.copy( forgetOne = v.toBoolean )
    case "prooftool"  => opts.copy( prooftool = v.toBoolean )
    case "fixup"      => opts.copy( fixup = v.toBoolean )
  }

  def parse( opts: Map[String, String] ) =
    opts.foldLeft( ViperOptions() )( ( opts_, opt ) => parseAndApply( opt._1, opt._2, opts_ ) )
}

class Viper( val ctx: Context, val sequent: HOLSequent, val options: ViperOptions ) extends Logger {
  implicit def ctx_ = ctx

  val Sequent( theory, Seq( conj @ All.Block( vs, _ ) ) ) = sequent
  val paramTypes = vs.map( _.ty ).map( _.asInstanceOf[TBase] )

  val instanceGen = new EnumeratingInstanceGenerator( paramTypes, implicitly )

  val encoding = InstanceTermEncoding( sequent.map( identity, instantiate( _, vs ) ) )

  type Instance = Seq[Expr]

  val grammarFinder = options.findingMethod match {
    case "maxsat" | "maxsatinst" =>
      val pi1QTys = options.quantTys getOrElse ( ctx.get[StructurallyInductiveTypes].constructors.keySet - "o" ).toSeq
      val msrsf = MaxSatRecSchemFinder( vs.map( _.ty ), pi1QTys.flatMap( ctx.get[BaseTypes].baseTypes.get ), encoding.instanceTermType,
        options.grammarWeighting, options.findingMethod == "maxsatinst",
        implicitly )

      info( "Recursion scheme template:" )
      for ( ( lhs, rhs ) <- msrsf.template.template.toSeq.sortBy( _._1.toString ) )
        info( s"$lhs -> $rhs" )

      msrsf
  }

  val smtSolver =
    if ( VeriT.isInstalled ) VeriT
    else new Escargot( splitting = true, propositional = true, equality = true )

  def solve(): LKProof = {
    info( sequent )

    val instanceProofs = mutable.Map[Instance, ExpansionProof]()
    for ( inst <- instanceGen.generate( options.instanceSize._1, options.instanceSize._2, options.instanceNumber ) )
      instanceProofs( inst ) = getInstanceProof( inst )

    while ( true ) {
      val spwi = findSPWI( instanceProofs )

      for ( ( inst, _ ) <- instanceProofs ) {
        val genLang = spwi.generatedLanguage( inst )
        require(
          smtSolver.isValid( And( genLang ) --> instantiate( conj, inst ) ),
          s"Generated instance language for $inst not tautological:\n${genLang.map( _.toSigRelativeString ).mkString( "\n" )}"
        )
      }

      findMinimalCounterexample( instanceProofs.keys, spwi ) match {
        case Some( inst ) =>
          instanceProofs( inst ) = getInstanceProof( inst )

        case None =>
          return solveSPWI( spwi )
      }
    }
    throw new IllegalArgumentException
  }

  def findSPWI( instanceProofs: Iterable[( Instance, ExpansionProof )] ): SchematicProofWithInduction = {
    val taggedLanguage =
      for {
        ( inst, es ) <- instanceProofs
        term <- encoding.encode( es.expansionSequent.antecedent ++: Sequent() )
      } yield inst -> term

    val spwi = grammarFinder.find( sequent, encoding, implicitly[Context], taggedLanguage.toSet )

    info( s"Found schematic proof with induction:\n$spwi\n" )
    for ( ( Apps( _, inst ), terms ) <- taggedLanguage groupBy { _._1 } ) {
      val genLang = spwi.generatedLanguage( inst ).map( encoding.encode )
      require(
        terms.map { _._2 }.toSet subsetOf genLang,
        s"Terms not covered by recursion scheme in $inst:\n${terms.map { _._2.toSigRelativeString }.mkString( "\n" )}"
      )
    }

    spwi
  }

  def findMinimalCounterexample( correctInstances: Iterable[Instance], spwi: SchematicProofWithInduction ): Option[Seq[Expr]] = {
    def checkInst( inst: Seq[Expr] ): Boolean = smtSolver.isValid( And( spwi.generatedLanguage( inst ) ) --> instantiate( conj, inst ) )
    val scale = ( 5 +: correctInstances.toSeq.map( folTermSize( _ ) ) ).max
    val testInstances =
      instanceGen.generate( 0, 5, 10 ) ++
        instanceGen.generate( options.tautCheckSize._1 * scale, options.tautCheckSize._2 * scale, options.tautCheckNumber )
    val failedInstOption = testInstances.toSeq.
      sortBy( folTermSize( _ ) ).view.
      filterNot { inst =>
        val ok = checkInst( inst )
        info( s"Checking validity for instance ${inst.map( _.toSigRelativeString )}: $ok" )
        ok
      }.headOption
    failedInstOption map { failedInst =>
      import cats.syntax.traverse._, cats.instances.list._
      val minimalCounterExample = failedInst.toList.
        traverse( i => folSubTerms( i ).filter( _.ty == i.ty ).toList ).
        filterNot( checkInst ).
        minBy { _ map { expressionSize( _ ) } sum }
      info( s"Minimal counterexample: ${minimalCounterExample.map { _.toSigRelativeString }}" )
      minimalCounterExample
    }
  }

  def solveSPWI( spwi: SchematicProofWithInduction ) = {
    val qbup @ Ex( x_B, qbupMatrix ) = spwi.solutionCondition
    info( s"Solution condition:\n${qbup.toSigRelativeString}\n" )

    val axiomArgs = for ( ( t, i ) <- paramTypes.zipWithIndex ) yield Var( s"y_$i", t )
    val canSolInst = instanceGen.generate( options.canSolSize._1, options.canSolSize._2, 1 ).head
    val pi1QTys = FunctionType.unapply( x_B.ty ).get._2.drop( axiomArgs.size + canSolInst.size )
    val ws = for ( ( t, i ) <- pi1QTys.zipWithIndex ) yield Var( s"w_$i", t )
    val xInst = x_B( axiomArgs: _* )( canSolInst: _* )( ws: _* ).asInstanceOf[Formula]

    info( s"Canonical solution at ${xInst.toSigRelativeString}:" )
    val canSol = hSolveQBUP.canonicalSolution( qbupMatrix, xInst )
    for ( cls <- CNFp( canSol ) )
      info( cls map { _.toSigRelativeString } )

    val Some( solution ) = hSolveQBUP( qbupMatrix, xInst, smtSolver )

    info( s"Found solution: ${solution.toSigRelativeString}\n" )

    val formula = BetaReduction.betaNormalize( instantiate( qbup, solution ) )
    require( smtSolver isValid skolemize( formula ), s"Solution not valid" )

    val proof = spwi.lkProof( Seq( solution ), EquationalLKProver )
    info( s"Found proof with ${proof.dagLike.size} inferences" )

    if ( options.prooftool ) prooftool( proof )

    ctx.check( proof )

    proof
  }

  def getInstanceProof( inst: Seq[Expr] ) = {
    info( s"Proving instance ${inst.map( _.toSigRelativeString )}" )
    val instanceSequent = sequent.map( identity, instantiate( _, inst ) )
    val instProof = options.instanceProver match {
      case "spass_pred" =>
        val reduction = GroundingReductionET |> CNFReductionExpRes |> PredicateReductionCNF |> ErasureReductionCNF
        val ( erasedCNF, back ) = reduction forward instanceSequent
        val Some( erasedProof ) = SPASS getResolutionProof erasedCNF
        val reifiedExpansion = back( erasedProof )
        reifiedExpansion
      case "spass_nopred" =>
        val reduction = GroundingReductionET |> ErasureReductionET
        val ( erasedInstanceSequent, back ) = reduction forward instanceSequent
        val erasedExpansion = SPASS getExpansionProof erasedInstanceSequent getOrElse {
          throw new IllegalArgumentException( s"Cannot prove:\n$erasedInstanceSequent" )
        }
        val reifiedExpansion = back( erasedExpansion )
        reifiedExpansion
      case "escargot" =>
        Escargot.getExpansionProof( instanceSequent ).get
    }
    require( smtSolver.isValid( instProof.deep ) )
    info( s"Instance proof for ${inst.map( _.toSigRelativeString )}:" )
    info( instProof.toSigRelativeString )
    info( "Language:" )
    encoding.encode( instProof ).toSeq.map( _.toString ).sorted.foreach( info( _ ) )

    instProof
  }

}

class ViperTactic( options: ViperOptions = ViperOptions() )( implicit ctx: Context ) extends at.logic.gapt.proofs.gaptic.Tactic[Unit] {
  import at.logic.gapt.proofs.gaptic._

  def copy( options: ViperOptions ) = new ViperTactic( options )

  def instanceNumber( n: Int ) = copy( options.copy( instanceNumber = n ) )
  def instanceSize( from: Float, to: Float ) = copy( options.copy( instanceSize = ( from, to ) ) )
  def instanceProver( prover: String ) = copy( options.copy( instanceProver = prover ) )
  def findingMethod( method: String ) = copy( options.copy( findingMethod = "maxsat" ) )
  def quantTys( tys: String* ) = copy( options.copy( quantTys = Some( tys ) ) )
  def grammarWeighting( w: Rule => Int ) = copy( options.copy( grammarWeighting = w ) )
  def tautCheckNumber( n: Int ) = copy( options.copy( tautCheckNumber = n ) )
  def tautCheckSize( from: Float, to: Float ) = copy( options.copy( tautCheckSize = ( from, to ) ) )
  def canSolSize( from: Float, to: Float ) = copy( options.copy( canSolSize = ( from, to ) ) )
  def doForgetOne( enable: Boolean = true ) = copy( options.copy( forgetOne = enable ) )

  override def apply( goal: OpenAssumption ): Either[TacticalFailure, ( Unit, LKProof )] = {
    val viper = new Viper( ctx, goal.conclusion, options )
    try {
      Right( () -> viper.solve() )
    } catch {
      case t: Throwable =>
        Left( TacticalFailure( this, t.toString ) )
    }
  }

  override def toString = options.toString
}

object Viper extends Logger {

  val optionRegex = """;\s*viper\s+([a-z]+)\s*([A-Za-z0-9,.]*)\s*""".r
  def extractOptions( tipSmtCode: InputFile ) =
    tipSmtCode.read.split( "\n" ).collect {
      case optionRegex( k, v ) => ( k, v )
    }
  def parseCode( tipSmtCode: InputFile, options: Map[String, String] ): ( TipProblem, ViperOptions ) = {
    val options_ = ViperOptions.parse(
      Map( "fixup" -> TipSmtParser.isInstalled.toString )
        ++ extractOptions( tipSmtCode ) ++ options
    )
    val problem =
      if ( options_.fixup ) TipSmtParser fixupAndParse tipSmtCode
      else TipSmtParser parse tipSmtCode
    ( problem, options_ )
  }
  val cmdLineOptRegex = """--([a-z]+)=(.*)""".r
  def parseArgs( args: Seq[String], options: Map[String, String] ): ( TipProblem, ViperOptions ) =
    args match {
      case Seq() =>
        println( "Usage: viper tip-problem.smt2" )
        sys exit 1
      case Seq( "-" ) =>
        parseCode( StringInputFile( Stream.continually( StdIn.readLine() ).takeWhile( _ != null ).mkString ), options )
      case Seq( fn ) =>
        parseCode( FilePath( fn ), options )
      case cmdLineOptRegex( k, v ) +: rest =>
        parseArgs( rest, options + ( k -> v ) )
    }

  def main( args: Array[String] ): Unit = {
    args match {
      case Array( "aip", _@ _* ) => aip.cli.aip.main( args.tail )
      case _ => {
        val ( problem, options ) = parseArgs( args, Map() )
        val viper = new Viper( problem.ctx, problem.toSequent, options )

        viper.makeVerbose()
        Logger.setConsolePattern( "%message%n" )

        viper.solve()
      }
    }
  }

}
