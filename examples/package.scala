package gapt

package object examples {
  val proofSequences = Seq[ProofSequence](
    LinearExampleProof,
    LinearCutExampleProof,
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
    FactorialFunctionEqualityExampleProof2 )
}

package examples {

  class Script extends scala.App {
    def run() = main( Array() )
  }

}
