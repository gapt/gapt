package gapt.prooftool


import gapt.formats.tptp.TptpFOLExporter
import gapt.proofs.{HOLSequent, Sequent, RichFormulaSequent}

import gapt.expr.formula.hol.existentialClosure


class ListViewer(name: String, list: List[HOLSequent]) extends ScrollableProofToolViewer[List[HOLSequent]](name, list) with Savable[List[HOLSequent]] {
  override type MainComponentType = DrawList
  override def createMainComponent = new DrawList(this, list)

  def saveFormats = Map(
    ".tptp" -> {
      (ls: List[HOLSequent]) => TptpFOLExporter(existentialClosure(ls.map(_.toImplication) ++: Sequent())).toString
    }
  )

}
