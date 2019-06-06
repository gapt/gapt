package gapt.formats.tip

import java.io.IOException

import gapt.formats.InputFile
import gapt.formats.StringInputFile
import gapt.formats.tip.compiler.TipSmtToTipProblemCompiler
import gapt.formats.tip.compiler.TipTransformationCompiler
import gapt.formats.tip.parser.TipSmtParser
import gapt.utils.ExternalProgram
import gapt.utils.runProcess

object TipSmtImporter extends ExternalProgram {

  def load( tipBench: InputFile ): TipProblem = {
    new TipTransformationCompiler( TipSmtParser.parse( tipBench ) )
      .compileTipProblem()
      .toProblem
  }

  def fixupAndLoad( tipBench: InputFile ): TipProblem =
    load( StringInputFile( runProcess(
      Seq(
        "tip",
        "--type-skolem-conjecture",
        "--commute-match",
        "--lambda-lift", "--axiomatize-lambdas",
        "--monomorphise",
        "--remove-builtin-bool",
        "--if-to-bool-op",
        "--int-to-nat",
        "--uncurry-theory",
        "--let-lift" ),
      tipBench.read,
      catchStderr = true ) ) )

  val isInstalled: Boolean =
    try { runProcess( Seq( "tip", "--help" ) ); true }
    catch { case _: IOException => false }
}
