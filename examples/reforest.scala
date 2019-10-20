package gapt.examples

import gapt.cutintro.{ CutIntroduction, ReforestMethod }
import gapt.grammars.reforest.Reforest
import gapt.proofs.expansion.InstanceTermEncoding
import gapt.utils.verbose
import sequence.LinearExampleProof
import sequence.SumExampleProof

object ReforestDemo extends Script {
  val ( lang, _ ) = InstanceTermEncoding(
    LinearExampleProof( 32 ) )

  val grammar = Reforest full Reforest.start( lang )
  println( grammar.toRecursionScheme )
  //  println( grammar.toVTRATG )

  verbose {
    CutIntroduction(
      SumExampleProof( 16 ),
      method = ReforestMethod )
  }
}
