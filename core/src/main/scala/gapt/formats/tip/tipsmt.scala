package gapt.formats.tip

import java.io.IOException

import gapt.formats.InputFile
import gapt.formats.StringInputFile
import gapt.formats.tip.compiler.TipSmtToTipProblemCompiler
import gapt.formats.tip.parser.TipSmtParser
import gapt.utils.ExternalProgram
import gapt.utils.runProcess

object find {
  def apply[T](
    elements: Seq[T], p: ( T ) => Boolean ): Option[( Seq[T], T, Seq[T] )] = {
    val index = elements.indexWhere( p )
    if ( index == -1 ) {
      None
    } else {
      Some( (
        elements.take( index ),
        elements( index ),
        elements.drop( index + 1 ) ) )
    }
  }
}

object TipSmtImporter extends ExternalProgram {

  def parse( tipBench: InputFile ): TipProblem = {
    ( new TipSmtToTipProblemCompiler( TipSmtParser.parse( tipBench ) ) )
      .compileTipProblem()
      .toProblem
  }

  def parse( input: String ): TipProblem = {
    parse( StringInputFile( input ) )
  }

  def fixupAndParse( tipBench: InputFile ): TipProblem =
    parse( StringInputFile( runProcess(
      Seq(
        "tip",
        "--type-skolem-conjecture",
        "--commute-match",
        "--lambda-lift", "--axiomatize-lambdas",
        "--monomorphise",
        "--if-to-bool-op",
        "--int-to-nat",
        "--uncurry-theory",
        "--let-lift" ),
      tipBench.read,
      catchStderr = true ) ) )

  val isInstalled =
    try { runProcess( Seq( "tip", "--help" ), "" ); true }
    catch { case _: IOException => false }
}
