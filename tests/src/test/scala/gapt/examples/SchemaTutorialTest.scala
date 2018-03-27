package gapt.examples

import gapt.proofs.gaptic.QedFailureException
import org.specs2.mutable.Specification

class SchemaTutorialTest extends Specification {

  def throwQedFailure =
    throwAn[ExceptionInInitializerError] like {
      case ex =>
        ex.getCause must beAnInstanceOf[QedFailureException]
    }

  "0" in { FirstSchema0; ok }
  "1" in { FirstSchema1; ok }
  "2" in { FirstSchema2; ok }
  "3" in { FirstSchema3; ok }
  "4" in { FirstSchema4 must throwQedFailure; ok }
  "5" in { FirstSchema5 must throwQedFailure; ok }
  "6" in { FirstSchema6; ok }
  "7" in { FirstSchema7; ok }
  "8" in { FirstSchema8; ok }
  "9" in { FirstSchema9; ok }

}
