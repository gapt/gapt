package gapt.formats.tip

import gapt.expr.Const
import gapt.expr.TBase
import gapt.expr.hol.instantiate
import gapt.formats.ClasspathInputFile
import gapt.provers.escargot.Escargot
import org.specs2.mutable.Specification

class TipSmtImporterTest extends Specification {

  "bin_distrib.smt2" in {
    val problem =
      TipSmtImporter.parse( ClasspathInputFile( "bin_distrib.smt2" ) )
    val one = Const( "One", TBase( "Bin" ) )
    val oneAnd = Const( "OneAnd", TBase( "Bin" ) ->: TBase( "Bin" ) )
    val instanceSequent =
      problem
        .toSequent
        .map(
          identity,
          instantiate( _, Seq( one, one, oneAnd( oneAnd( one ) ) ) ) )
    Escargot getResolutionProof instanceSequent must beSome
  }

}
