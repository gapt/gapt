package at.logic.gapt.formats.tip

import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.expr.{ TBase, Const }
import at.logic.gapt.provers.escargot.Escargot
import org.specs2.mutable._

import scala.io.Source

class TipSmtParserTest extends Specification {

  "bin_distrib.smt2" in {
    val problem = TipSmtParser.parse( Source.fromInputStream( getClass.getClassLoader.getResourceAsStream( "bin_distrib.smt2" ) ).mkString )
    val one = Const( "One", TBase( "Bin" ) )
    val oneAnd = Const( "OneAnd", TBase( "Bin" ) -> TBase( "Bin" ) )
    val instanceSequent = problem.toSequent.map( identity, instantiate( _, Seq( one, one, oneAnd( oneAnd( one ) ) ) ) )
    Escargot getRobinsonProof instanceSequent must beSome
  }

}
