package at.logic.gapt.provers.viper

import ammonite.ops._
import at.logic.gapt.formats.tip.{ TipProblem, TipSmtParser }
import at.logic.gapt.formats.{ InputFile, StringInputFile }
import at.logic.gapt.grammars.Rule
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.provers.Prover
import at.logic.gapt.provers.viper.grammars._
import at.logic.gapt.utils.Logger

import scala.io.StdIn

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
  def parseCode( tipSmtCode: InputFile, options: Map[String, String] ): ( TipProblem, TreeGrammarProverOptions ) = {
    val options_ = TreeGrammarProverOptions.parse(
      Map( "fixup" -> TipSmtParser.isInstalled.toString )
        ++ extractOptions( tipSmtCode ) ++ options
    )
    val problem =
      if ( options_.fixup ) TipSmtParser fixupAndParse tipSmtCode
      else TipSmtParser parse tipSmtCode
    ( problem, options_ )
  }
  val cmdLineOptRegex = """--([a-z]+)=(.*)""".r
  def parseArgs( args: Seq[String], options: Map[String, String] ): ( TipProblem, TreeGrammarProverOptions ) =
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
        val viper = new TreeGrammarProver( problem.ctx, problem.toSequent, options )

        viper.makeVerbose()
        Logger.setConsolePattern( "%message%n" )

        viper.solve()
      }
    }
  }

}
