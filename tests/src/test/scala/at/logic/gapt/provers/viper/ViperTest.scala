package at.logic.gapt.provers.viper

import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.{ Sequent, SequentMatchers }
import at.logic.gapt.provers.viper.grammars.TreeGrammarProver
import org.specs2.mutable.Specification
import org.specs2.specification.core.Fragments

class ViperTest extends Specification with SequentMatchers {

  "known to be working problems" in {
    Fragments.foreach( Seq(
      "appnil",
      "comm", "comm1", "commsx", "comms0",
      "general", "generaldiffconcl", "linear",
      "linear2par",
      "square",
      "minus", "plus0",
      "prod_prop_31", "prod_prop_31_monomorphic"
    ) ) { prob =>
      prob in {
        var opts0 = ViperOptions( fixup = false )
        if ( prob == "linear2par" )
          skipped( "needs careful choice of instance for canonical substitution" )
        if ( prob == "prod_prop_31" ) {
          if ( !TipSmtParser.isInstalled )
            skipped( "tip tool required for preprocessing" )
          opts0 = opts0.copy( fixup = true )
        }
        val file = ClasspathInputFile( s"induction/$prob.smt2" )
        val ( Nil, options ) = ViperOptions.parse( Viper.extractOptions( file ), opts0 )
        val problem = if ( options.fixup ) TipSmtParser.fixupAndParse( file ) else TipSmtParser.parse( file )
        val lk = new TreeGrammarProver( problem.ctx, problem.toSequent, options.treeGrammarProverOptions ).solve()
        problem.ctx check lk
        lk.conclusion.distinct.diff( problem.toSequent ) must_== Sequent()
      }
    }
  }

}
