package at.logic.gapt.examples

import at.logic.gapt.cutintro.{ ExternalReforestMethod, ReforestMethod, CutIntroduction }
import at.logic.gapt.grammars.reforest.Reforest
import at.logic.gapt.proofs.expansion.{ InstanceTermEncoding, FOLInstanceTermEncoding }

object ReforestDemo extends Script {
  val ( lang, _ ) = FOLInstanceTermEncoding(
    LinearExampleProof( 32 )
  )

  val grammar = Reforest full Reforest.start( lang )
  println( grammar.toRecursionScheme )
  //  println( grammar.toVTRATG )

  CutIntroduction.compressLKProof(
    SumExampleProof( 16 ),
    method = ReforestMethod,
    verbose = true
  )
}
