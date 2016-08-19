package at.logic.gapt.provers.viper

import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.provers.smtlib.Z3
import at.logic.gapt.provers.spass.SPASS
import org.specs2.mutable.Specification
import org.specs2.specification.core.Fragments

class ViperTest extends Specification {

  "known to be working problems" in {
    Fragments.foreach( Seq(
      "appnil",
      "comm", "comm1", "commsx",
      "general", "generaldiffconcl", "linear",
      "square",
      "minus", "plus0",
      "prod_prop_31", "prod_prop_31_monomorphic"
    ) ) { prob =>
      prob in {
        var extraOptions = Map( "verbose" -> "false", "fixup" -> "false" )
        if ( prob == "prod_prop_31" ) {
          if ( !TipSmtParser.isInstalled )
            skipped( "tip tool required for preprocessing" )
          extraOptions += "fixup" -> "true"
        }
        val ( problem, options ) = Viper.parseCode(
          ClasspathInputFile( s"induction/$prob.smt2" ),
          extraOptions
        )
        val lk = new Viper( problem, options ).solve()
        ok
      }
    }
  }

}
