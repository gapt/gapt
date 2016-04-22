package at.logic.gapt.provers.viper

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ CNFp, instantiate }
import at.logic.gapt.formats.tip.{ TipProblem, TipSmtParser }
import at.logic.gapt.grammars.{ RecursionScheme, instantiateRS }
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
  instanceNumber:  Int,
  instanceSize:    FloatRange,
  quantTys:        Option[Seq[TBase]],
  tautCheckNumber: Int,
  tautCheckSize:   FloatRange,
  canSolSize:      FloatRange,
  forgetOne:       Boolean,
  verbose:         Boolean
)
object ViperOptions {
  type FloatRange = ( Float, Float )

  private def parseRange( ran: String ): FloatRange = {
    val Seq( from, to ) = ran.split( "," ).toSeq
    from.toFloat -> to.toFloat
  }

  def parse( opts: Map[String, String] ) =
    ViperOptions(
      verbose = opts.getOrElse( "verbose", "true" ).toBoolean,
      instanceNumber = opts.getOrElse( "instnum", "3" ).toInt,
      instanceSize = parseRange( opts.getOrElse( "instsize", "0,3" ) ),
      quantTys = opts.get( "qtys" ).map( _.split( "," ).toSeq.filter( _.nonEmpty ).map( TBase ) ),
      tautCheckNumber = opts.getOrElse( "tchknum", "20" ).toInt,
      tautCheckSize = parseRange( opts.getOrElse( "tchksize", "6,10" ) ),
      canSolSize = parseRange( opts.getOrElse( "cansolsize", "2,4" ) ),
      forgetOne = opts.getOrElse( "forgetone", "false" ).toBoolean
    )

}

class Viper( val problem: TipProblem, val options: ViperOptions ) {
  implicit var ctx = problem.context

  val sequent @ Sequent( theory, Seq( All.Block( vs, _ ) ) ) = problem.toSequent
  val paramTypes = vs.map( _.exptype ).map( _.asInstanceOf[TBase] )

  def info() = if ( options.verbose ) println()
  def info( msg: Any ) = if ( options.verbose ) println( msg )

  def inside( range: FloatRange ) = ( f: Float ) => range._1 <= f && f <= range._2
  val encoding = InstanceTermEncoding( sequent.map( identity, instantiate( _, vs ) ) )

  type Instance = Seq[LambdaExpression]

  def solve(): LambdaExpression = {
    info( sequent )
    info()

    val instanceProofs = mutable.Map[Instance, ExpansionProof]()
    while ( instanceProofs.size < options.instanceNumber ) {
      val inst = randomInstance.generate( paramTypes, inside( options.instanceSize ) )
      if ( !instanceProofs.contains( inst ) )
        instanceProofs( inst ) = getInstanceProof( inst )
    }

    while ( true ) {
      val rs = findRecursionScheme( instanceProofs )
      findMinimalCounterexample( rs ) match {
        case Some( inst ) =>
          instanceProofs( inst ) = getInstanceProof( inst )

        case None =>
          return solveRecSchem( rs )
      }
    }
    throw new IllegalArgumentException
  }

  def findRecursionScheme( instanceProofs: Iterable[( Instance, ExpansionProof )] ): RecursionScheme = {
    val A = Const( "A", FunctionType( encoding.instanceTermType, paramTypes ) )

    val pi1QTys = options.quantTys getOrElse {
      ctx.typeDefs.toSeq collect {
        case InductiveType( ty, _ ) if ty != To => ty
      }
    }

    val template = simplePi1RecSchemTempl( A( vs: _* ), pi1QTys )
    info( "Recursion scheme template:" )
    for ( ( lhs, rhs ) <- template.template.toSeq.sortBy { _._1.toString } )
      info( s"$lhs -> $rhs" )
    info()

    val targets = for ( ( inst, es ) <- instanceProofs; term <- encoding encode es ) yield A( inst: _* ) -> term
    val rs = template.findMinimalCoverViaInst( targets.toSet, weight = rule => expressionSize( rule.lhs === rule.rhs ) )
    info( s"Minimized recursion scheme:\n$rs\n" )

    val logicalRS = homogenizeRS( encoding decode rs )
    info( s"Logical recursion scheme:\n$logicalRS\n" )
    logicalRS
  }

  def findMinimalCounterexample( logicalRS: RecursionScheme ): Option[Seq[LambdaExpression]] = {
    def checkInst( inst: Seq[LambdaExpression] ): Boolean = Z3 isValid Or( logicalRS.parametricLanguage( inst: _* ) )
    val failedInstOption = ( 0 to options.tautCheckNumber ).view.
      map { _ => randomInstance.generate( paramTypes, inside( options.tautCheckSize ) ) }.
      distinct.
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

  def solveRecSchem( logicalRS: RecursionScheme ) = {

    val qbup @ Ex( x_G, qbupMatrix ) = qbupForRecSchem( logicalRS )
    info( s"QBUP:\n${qbup.toSigRelativeString}\n" )

    val canSolInst = randomInstance.generate( paramTypes, inside( options.canSolSize ) )
    info( s"Canonical solution at G($canSolInst,w):" )
    val G_ = logicalRS.nonTerminals.find( _.name == "G" ).get
    val pi1QTys = FunctionType.unapply( G_.exptype ).get._2.drop( canSolInst.size )
    val ws = for ( ( t, i ) <- pi1QTys.zipWithIndex ) yield Var( s"w$i", t )
    val canSol = And( logicalRS generatedTerms G_( canSolInst: _* )( ws: _* ) map { -_ } )
    for ( cls <- CNFp.toClauseList( canSol ) )
      info( cls map { _.toSigRelativeString } )
    info()

    val Some( solution ) = hSolveQBUP( qbupMatrix, x_G( canSolInst: _* )( ws: _* ), canSol, forgetOne = options.forgetOne )
    info()

    val formula = BetaReduction.betaNormalize( instantiate( qbup, solution ) )
    info( s"Solution: ${solution.toSigRelativeString}\n" )
    info( Z3 isValid skolemize( formula ) )

    solution
  }

  def getInstanceProof( inst: Seq[LambdaExpression] ) = {
    info( s"Proving instance ${inst.map( _.toSigRelativeString )}" )
    val instanceSequent = sequent.map( identity, instantiate( _, inst ) )
    val instProof = if ( true ) {
      if ( false ) {
        val reduction = GroundingReductionET |> CNFReductionExpRes |> PredicateReductionCNF |> ErasureReductionCNF
        val ( erasedCNF, back ) = reduction forward instanceSequent
        val Some( erasedProof ) = SPASS getRobinsonProof erasedCNF
        val reifiedExpansion = back( erasedProof )
        reifiedExpansion
      } else {
        val reduction = GroundingReductionET |> ErasureReductionET
        val ( erasedInstanceSequent, back ) = reduction forward instanceSequent
        val erasedExpansion = SPASS getExpansionProof erasedInstanceSequent getOrElse {
          throw new IllegalArgumentException( s"Cannot prove:\n$erasedInstanceSequent" )
        }
        val reifiedExpansion = back( erasedExpansion )
        require( Z3 isValid reifiedExpansion.deep )
        reifiedExpansion
      }
    } else {
      Escargot.getExpansionProof( instanceSequent ).get
    }
    info( s"Instances for x = ${inst.map( _.toSigRelativeString )}:" )
    info( extractInstances( instProof ).map( _.toSigRelativeString ) )
    info()

    instProof
  }

}

object Viper {

  val optionRegex = """;\s*viper\s+([a-z]+)\s*([A-Za-z0-9,]*)\s*""".r
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
