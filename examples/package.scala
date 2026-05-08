package gapt

import gapt.examples.sequence._

package object examples {
  val proofSequences = Seq[ProofSequence](
    LinearExampleProof,
    LinearCutExampleProof,
    LinearRightCutExampleProof,
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
