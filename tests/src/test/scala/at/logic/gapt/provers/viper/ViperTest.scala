package at.logic.gapt.provers.viper

import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.provers.smtlib.Z3
import at.logic.gapt.provers.spass.SPASS
import org.specs2.mutable.Specification
import org.specs2.specification.core.Fragments

class ViperTest extends Specification {

  "known to be working problems" in {
    Fragments.foreach( Seq(
      "appnil", "comm", "general", "generaldiffconcl", "linear", "prod_prop_31"
    ) ) { prob =>
      prob in {
        if ( !SPASS.isInstalled || !Z3.isInstalled || !TipSmtParser.isInstalled ) skipped
        val ( problem, options ) = Viper.parseCode(
          io.Source.fromInputStream( getClass.getClassLoader.getResourceAsStream( s"induction/$prob.smt2" ) ).mkString,
          Map( "verbose" -> "false" )
        )
        new Viper( problem, options ).solve()
        ok
      }
    }
  }

}
