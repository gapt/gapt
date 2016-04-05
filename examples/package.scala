package at.logic.gapt

package object examples {
  val proofSequences = Seq[ProofSequence](
    LinearExampleProof,
    LinearEqExampleProof,
    SquareDiagonalExampleProof,
    SquareEdgesExampleProof,
    SquareEdges2DimExampleProof,
    SumExampleProof,
    SumOfOnesF2ExampleProof,
    SumOfOnesFExampleProof,
    SumOfOnesExampleProof,
    UniformAssociativity3ExampleProof,
    FactorialFunctionEqualityExampleProof,
    FactorialFunctionEqualityExampleProof2
  )
}

package examples {

  import at.logic.gapt.proofs.FiniteContext

  class Script extends scala.App {
    def run() = main( Array() )
  }

}
