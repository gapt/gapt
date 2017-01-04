package at.logic.gapt.examples

import at.logic.gapt.cutintro.{ ReforestMethod, CutIntroduction }
import at.logic.gapt.grammars.reforest.Reforest
import at.logic.gapt.proofs.expansion.InstanceTermEncoding

object ReforestDemo extends Script {
  val ( lang, _ ) = InstanceTermEncoding(
    LinearExampleProof( 32 )
  )

  val grammar = Reforest full Reforest.start( lang )
  println( grammar.toRecursionScheme )
  //  println( grammar.toVTRATG )

  CutIntroduction.makeVerbose()
  CutIntroduction(
    SumExampleProof( 16 ),
    method = ReforestMethod
  )
}
