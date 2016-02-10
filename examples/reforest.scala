package at.logic.gapt.examples

import at.logic.gapt.grammars.reforest.Reforest
import at.logic.gapt.proofs.expansion.FOLInstanceTermEncoding

object ReforestDemo extends Script {
  val ( lang, _ ) = FOLInstanceTermEncoding(
    SumExampleProof( 100 )
  )

  val grammar = Reforest full Reforest.start( lang )

  println( grammar )
}
