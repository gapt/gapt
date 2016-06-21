package at.logic.gapt.provers.viper

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ CNFp, instantiate }
import at.logic.gapt.formats.tip.{ TipProblem, TipSmtParser }
import at.logic.gapt.grammars.{ RecursionScheme, Rule, instantiateRS }
import at.logic.gapt.proofs.Context.InductiveType
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.expansion.{ ExpansionProof, InstanceTermEncoding, extractInstances }
import at.logic.gapt.proofs.lk.skolemize
import at.logic.gapt.proofs.reduction._
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.smtlib.Z3
import at.logic.gapt.provers.spass.SPASS
import at.logic.gapt.provers.viper.ViperOptions.FloatRange

import scala.collection.mutable
import scala.io.{ Source, StdIn }

case class ViperOptions(
  instanceNumber:   Int                = 3,
  instanceSize:     FloatRange         = ( 0, 3 ),
  instanceProver:   String             = "spass_nopred",
  findingMethod:    String             = "maxsat",
  quantTys:         Option[Seq[TBase]] = None,
  grammarWeighting: Rule => Int        = _ => 1,
  tautCheckNumber:  Int                = 20,
  tautCheckSize:    FloatRange         = ( 2, 3 ),
  canSolSize:       FloatRange         = ( 2, 4 ),
  forgetOne:        Boolean            = false,
  verbose:          Boolean            = true
)
object ViperOptions {
  type FloatRange = ( Float, Float )

  private def parseRange( ran: String ): FloatRange = {
    val Seq( from, to ) = ran.split( "," ).toSeq
    from.toFloat -> to.toFloat
  }

  private def parseAndApply( k: String, v: String, opts: ViperOptions ): ViperOptions = k match {
    case "verbose"    => opts.copy( verbose = v.toBoolean )
    case "instnum"    => opts.copy( instanceNumber = v.toInt )
    case "instsize"   => opts.copy( instanceSize = parseRange( v ) )
    case "instprover" => opts.copy( instanceProver = v )
    case "findmth"    => opts.copy( findingMethod = v )
    case "qtys"       => opts.copy( quantTys = Some( v.split( "," ).toSeq.filter( _.nonEmpty ).map( TBase ) ) )
    case "gramw" => v match {
      case "scomp"  => opts.copy( grammarWeighting = r => randomInstance.exprSize( r.lhs ) + randomInstance.exprSize( r.rhs ) )
      case "nprods" => opts.copy( grammarWeighting = _ => 1 )
    }
    case "tchknum"    => opts.copy( tautCheckNumber = v.toInt )
    case "tchksize"   => opts.copy( tautCheckSize = parseRange( v ) )
    case "cansolsize" => opts.copy( canSolSize = parseRange( v ) )
    case "forgetone"  => opts.copy( forgetOne = v.toBoolean )
  }

  def parse( opts: Map[String, String] ) =
    opts.foldLeft( ViperOptions() )( ( opts_, opt ) => parseAndApply( opt._1, opt._2, opts_ ) )
}

class Viper( val problem: TipProblem, val options: ViperOptions ) {
  implicit var ctx = problem.context

  val sequent @ Sequent( theory, Seq( All.Block( vs, _ ) ) ) = problem.toSequent
  val paramTypes = vs.map( _.exptype ).map( _.asInstanceOf[TBase] )

  def info() = if ( options.verbose ) println()
  def info( msg: Any ) = if ( options.verbose ) println( msg )

  def inside( range: FloatRange, scale: Float = 1 ) = ( f: Float ) => scale * range._1 <= f && f <= scale * range._2
  val encoding = InstanceTermEncoding( sequent.map( identity, instantiate( _, vs ) ) )

  type Instance = Seq[LambdaExpression]

  val grammarFinder = options.findingMethod match {
    case "maxsat" =>
      val pi1QTys = options.quantTys getOrElse {
        ctx.typeDefs.toSeq collect { case InductiveType( ty, _ ) if ty != To => ty }
      }

      val msrsf = MaxSatRecSchemFinder( vs.map( _.exptype ), pi1QTys, encoding.instanceTermType, options.grammarWeighting, implicitly )

      info( "Recursion scheme template:" )
      for ( ( lhs, rhs ) <- msrsf.template.template.toSeq.sortBy( _._1.toString ) )
        info( s"$lhs -> $rhs" )
      info()

      msrsf
  }

  def solve(): LambdaExpression = {
    info( sequent )
    info()

    val instanceProofs = mutable.Map[Instance, ExpansionProof]()
    var ttl = options.instanceNumber * 10
    while ( instanceProofs.size < options.instanceNumber && ttl > 0 ) {
      ttl -= 1
      val inst = randomInstance.generate( paramTypes, inside( options.instanceSize ) )
      if ( !instanceProofs.contains( inst ) )
        instanceProofs( inst ) = getInstanceProof( inst )
    }

    while ( true ) {
      val rs = findRecursionScheme( instanceProofs )

      for ( ( inst, _ ) <- instanceProofs ) {
        val genLang = rs.parametricLanguage( inst: _* )
        require( Z3 isValid Or( genLang ), s"Generated instance language for $inst not tautological" )
      }

      findMinimalCounterexample( instanceProofs.keys, rs ) match {
        case Some( inst ) =>
          instanceProofs( inst ) = getInstanceProof( inst )

        case None =>
          return solveRecSchem( rs )
      }
    }
    throw new IllegalArgumentException
  }

  def findRecursionScheme( instanceProofs: Iterable[( Instance, ExpansionProof )] ): RecursionScheme = {
    val taggedLanguage =
      for {
        ( inst, es ) <- instanceProofs
        term <- encoding.encode( es.expansionSequent.antecedent ++: Sequent() )
      } yield inst -> term

    val rsWithoutConclusion = grammarFinder.find( taggedLanguage.toSet )

    val conclusions =
      for {
        ( inst, es ) <- instanceProofs
        term <- encoding.encode( Sequent() :++ es.expansionSequent.succedent )
      } yield Rule( rsWithoutConclusion.axiom( vs ), term )
    val rs = rsWithoutConclusion.copy( rules = rsWithoutConclusion.rules ++ conclusions )

    info( s"Found recursion scheme:\n$rs\n" )
    for ( ( Apps( _, inst ), terms ) <- taggedLanguage groupBy { _._1 } ) {
      val genLang = rs.parametricLanguage( inst: _* )
      require(
        terms.map { _._2 }.toSet subsetOf genLang,
        s"Terms not covered by recursion scheme in $inst:\n${terms.map { _._2.toSigRelativeString }.mkString( "\n" )}"
      )
    }

    val logicalRS = encoding decode rs
    info( s"Logical recursion scheme:\n$logicalRS\n" )
    logicalRS
  }

  def findMinimalCounterexample( correctInstances: Iterable[Instance], logicalRS: RecursionScheme ): Option[Seq[LambdaExpression]] = {
    def checkInst( inst: Seq[LambdaExpression] ): Boolean = Z3 isValid Or( logicalRS.parametricLanguage( inst: _* ) )
    val scale = ( 5 +: correctInstances.toSeq.map( _.map( randomInstance.exprSize ).sum ) ).max
    val failedInstOption = ( 0 to options.tautCheckNumber ).
      map { _ => randomInstance.generate( paramTypes, inside( options.tautCheckSize, scale ) ) }.
      distinct.sortBy { _.map( randomInstance.exprSize ).sum }.view.
      filterNot { inst =>
        val ok = checkInst( inst )
        info( s"Checking validity for instance ${inst.map( _.toSigRelativeString )}: $ok" )
        ok
      }.headOption
    failedInstOption map { failedInst =>
      import scalaz._
      import Scalaz._
      val minimalCounterExample = failedInst.toList.
        traverse( i => instantiateRS.subTerms( i ).filter( _.exptype == i.exptype ).toList ).
        filterNot { i => Z3 isValid Or( logicalRS.parametricLanguage( i: _* ) ) }.
        minBy { _ map { expressionSize( _ ) } sum }
      info( s"Minimal counterexample: ${minimalCounterExample.map { _.toSigRelativeString }}" )
      minimalCounterExample
    }
  }

  def solveRecSchem( rs: RecursionScheme ) = {
    val homogenized = homogenizeRS( rs )

    val qbup @ Ex( x_G, qbupMatrix ) = qbupForRecSchem( homogenized )
    info( s"QBUP:\n${qbup.toSigRelativeString}\n" )

    val axiomArgs = homogenized.rules.collectFirst { case Rule( Apps( Const( "A", _ ), args ), _ ) => args }.get

    val canSolInst = randomInstance.generate( paramTypes, inside( options.canSolSize ) )
    info( s"Canonical solution at $canSolInst:" )
    val B = homogenized.nonTerminals.find( _.name == "B" ).get
    val pi1QTys = FunctionType.unapply( B.exptype ).get._2.drop( axiomArgs.size + canSolInst.size )
    val ws = for ( ( t, i ) <- pi1QTys.zipWithIndex ) yield Var( s"w$i", t )
    val canSol = And( homogenized generatedTerms B( axiomArgs: _* )( canSolInst: _* )( ws: _* ) map { -_ } )
    for ( cls <- CNFp.toClauseList( canSol ) )
      info( cls map { _.toSigRelativeString } )
    info()

    val Some( solution ) = hSolveQBUP( qbupMatrix, x_G( axiomArgs: _* )( canSolInst: _* )( ws: _* ), canSol, forgetOne = options.forgetOne )
    info()

    val formula = BetaReduction.betaNormalize( instantiate( qbup, solution ) )
    info( s"Found solution: ${solution.toSigRelativeString}\n" )
    info( Z3 isValid skolemize( formula ) )

    solution
  }

  def getInstanceProof( inst: Seq[LambdaExpression] ) = {
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
    require( Z3 isValid instProof.deep )
    info( s"Instance proof for ${inst.map( _.toSigRelativeString )}:" )
    info( instProof.toSigRelativeString )
    info( "Language:" )
    encoding.encode( instProof ).toSeq.map( _.toString ).sorted.foreach( info )
    info()

    instProof
  }

}

object Viper {

  val optionRegex = """;\s*viper\s+([a-z]+)\s*([A-Za-z0-9,.]*)\s*""".r
  def extractOptions( tipSmtCode: String ) =
    tipSmtCode.split( "\n" ).collect {
      case optionRegex( k, v ) => ( k, v )
    }
  def parseCode( tipSmtCode: String, options: Map[String, String] ): ( TipProblem, ViperOptions ) = {
    val options_ = options ++ extractOptions( tipSmtCode )
    val problem =
      if ( options_ contains "nofixup" ) TipSmtParser parse tipSmtCode
      else TipSmtParser fixupAndParse tipSmtCode
    ( problem, ViperOptions parse options_ )
  }
  val cmdLineOptRegex = """--([a-z]+)=(.*)""".r
  def parseArgs( args: Seq[String], options: Map[String, String] ): ( TipProblem, ViperOptions ) =
    args match {
      case Seq() =>
        println( "Usage: viper tip-problem.smt2" )
        sys exit 1
      case Seq( "-" ) =>
        parseCode( Stream.continually( StdIn.readLine() ).takeWhile( _ != null ).mkString, options )
      case Seq( fn ) =>
        parseCode( Source fromFile fn mkString, options )
      case cmdLineOptRegex( k, v ) +: rest =>
        parseArgs( rest, options + ( k -> v ) )
    }

  def main( args: Array[String] ): Unit = {
    val ( problem, options ) = parseArgs( args, Map() )
    new Viper( problem, options ).solve()
  }

}
