package at.logic.gapt.formats.tip

import at.logic.gapt.expr.fol.reduceHolToFol
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.expr.{ Tdata, Const }
import at.logic.gapt.provers.prover9.Prover9
import org.specs2.mutable._

import scala.io.Source

class TipSmtParserTest extends Specification {

  "bin_distrib.smt2" in {
    val problem = TipSmtParser.parse( Source.fromInputStream( getClass.getClassLoader.getResourceAsStream( "bin_distrib.smt2" ) ).mkString )
    problem.toSequent
    ok
  }

  "bin_distrib.smt2 instance validity" in {
    if ( !Prover9.isInstalled ) skipped
    val problem = TipSmtParser.parse( Source.fromInputStream( getClass.getClassLoader.getResourceAsStream( "bin_distrib.smt2" ) ).mkString )
    val one = Const( "One", Tdata( "Bin" ) )
    val oneAnd = Const( "OneAnd", Tdata( "Bin" ) -> Tdata( "Bin" ) )
    val instanceSequent = problem.toSequent.map( identity, instantiate( _, Seq( one, one, oneAnd( oneAnd( one ) ) ) ) )
    Prover9 getRobinsonProof reduceHolToFol( instanceSequent ) must beSome
  }

}
