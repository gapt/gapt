package at.logic.gapt.examples

import at.logic.gapt.proofs.nd._
import at.logic.gapt.proofs.Context

object example1 extends Script {

  var ctx = Context()

  implicit var systemT = ClassicalExtraction.systemT( ctx )
  println( systemT )

}
