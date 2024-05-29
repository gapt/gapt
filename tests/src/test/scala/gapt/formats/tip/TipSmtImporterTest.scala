package gapt.formats.tip

import gapt.expr.Const
import gapt.expr.formula.hol.instantiate
import gapt.expr.ty.TBase
import gapt.formats.ClasspathInputFile
import gapt.provers.escargot.Escargot
import org.specs2.mutable.Specification

class TipSmtImporterTest extends Specification {

  "bin_distrib.smt2" in {
    val problem =
      TipSmtImporter.load(ClasspathInputFile("bin_distrib.smt2"))
    val one = Const("One", TBase("Bin"))
    val oneAnd = Const("OneAnd", TBase("Bin") ->: TBase("Bin"))
    val instanceSequent =
      problem
        .toSequent
        .map(
          identity,
          instantiate(_, Seq(one, one, oneAnd(oneAnd(one))))
        )
    Escargot getResolutionProof instanceSequent must beSome
  }

}
