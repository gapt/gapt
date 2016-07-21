package at.logic.gapt.formats.tip

import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.expr.{ Const, TBase }
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.provers.escargot.Escargot
import org.specs2.mutable._

import scala.io.Source

class TipSmtParserTest extends Specification {

  "bin_distrib.smt2" in {
    val problem = TipSmtParser.parse( ClasspathInputFile( "bin_distrib.smt2" ) )
    val one = Const( "One", TBase( "Bin" ) )
    val oneAnd = Const( "OneAnd", TBase( "Bin" ) -> TBase( "Bin" ) )
    val instanceSequent = problem.toSequent.map( identity, instantiate( _, Seq( one, one, oneAnd( oneAnd( one ) ) ) ) )
    Escargot getResolutionProof instanceSequent must beSome
  }

}
