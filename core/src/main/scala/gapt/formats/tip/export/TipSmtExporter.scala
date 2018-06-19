package gapt.formats.tip.export

import gapt.formats.tip.TipProblem
import gapt.formats.tip.parser.TipSmtProblem
import gapt.formats.tip.parser.toSExpression
import gapt.formats.tip.parser.toTipAst
import gapt.utils.Doc

object TipSmtExporter {

  def export( problem: TipSmtProblem ): Doc = {
    Doc.stack( toSExpression( problem ).map { _.toDoc } )
  }

  def export( problem: TipProblem ): Doc = {
    Doc.stack( toSExpression( problem ).map { _.toDoc } )
  }
}
