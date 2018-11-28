package gapt.provers.viper

import gapt.examples.induction._
import gapt.formats.ClasspathInputFile
import gapt.formats.tip.TipSmtImporter
import gapt.proofs.{ Sequent, SequentMatchers }
import gapt.provers.spass.SPASS
import gapt.provers.viper.grammars.TreeGrammarProver
import org.specs2.mutable.Specification
import org.specs2.specification.core.Fragments

class ViperTest extends Specification with SequentMatchers {

  val optionsRegex = """;.*viper\s+(.*)""".r.unanchored
  def extractOptions( contents: String ): List[String] =
    contents match {
      case optionsRegex( opts ) =>
        opts.split( " " ).toList.map { case "\"\"" => "" case a => a }
      case _ => Nil
    }

  "known to be working problems" in {
    Fragments.foreach( Seq(
      "appnil",
      "comm", "comm1", "commsx", "comms0",
      "general", "generaldiffconcl", "linear",
      "linear2par",
      "square",
      "minus", "plus0",
      "prod_prop_31", "prod_prop_31_monomorphic" ) ) { prob =>
      prob in {
        var opts0 = ViperOptions( fixup = false )
        if ( prob == "linear2par" ) skipped( "multi-parameter not integrated here" )
        if ( prob == "prod_prop_31" ) {
          skipped( "tip tools horribly broken" )
          if ( !TipSmtImporter.isInstalled )
            skipped( "tip tool required for preprocessing" )
          opts0 = opts0.copy( fixup = true )
        }
        val file = ClasspathInputFile( s"induction/$prob.smt2" )
        val ( Nil, options ) = ViperOptions.parse( extractOptions( file.read ), opts0 )
        val problem = if ( options.fixup ) TipSmtImporter.fixupAndLoad( file ) else TipSmtImporter.load( file )
        val lk = new TreeGrammarProver( problem.ctx, problem.toSequent, options.treeGrammarProverOptions ).solve()
        problem.ctx check lk
        lk.conclusion.distinct.diff( problem.toSequent ) must_== Sequent()
      }
    }
  }

  "associativity special case" in {
    if ( !SPASS.isInstalled ) skipped( "required instance proofs from spass" )
    associativitySpecialCase; ok
  }

  "associativity" in { associativity; ok }
  "comm" in { comm; ok }

}
