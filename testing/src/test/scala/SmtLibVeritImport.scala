package at.logic.testing.verit

import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.formats.veriT.VeriTParser
import at.logic.gapt.provers.minisat._
import at.logic.testing.{ skipIfRunsLongerThan, recursiveListFiles }

import org.specs2.mutable._
import org.specs2.specification.core.Fragment
import scala.concurrent.duration._

trait SmtLibVeritSpec {
  def veritProofs = recursiveListFiles( "testing/veriT-SMT-LIB" ).filter( _.getName.endsWith( ".proof_flat" ) )
}

class SmtLibVeritImport extends Specification with SmtLibVeritSpec {
  "SMT-LIB VeriT proof import" should {
    Fragment.foreach( veritProofs ) { file =>
      file.getName in {
        skipIfRunsLongerThan( 1 minute ) {
          VeriTParser.getExpansionProof( file.getAbsolutePath )
          ok
        }
      }
    }
  }
}

class SmtLibVeritImportValidation extends Specification with SmtLibVeritSpec {
  "SMT-LIB VeriT proof import and validation" should {
    Fragment.foreach( veritProofs ) { file =>
      file.getName in {
        skipIfRunsLongerThan( 2 minute ) {
          val E = VeriTParser.getExpansionProof( file.getAbsolutePath )
          E.isDefined must beTrue
          val deep = toDeep( E.get ).toFormula
          ( new MiniSATProver ).isValid( deep ) must beTrue
          ok
        }
      }
    }
  }
}

