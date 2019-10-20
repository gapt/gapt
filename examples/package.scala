package gapt

import sequence.FactorialFunctionEqualityExampleProof
import sequence.FactorialFunctionEqualityExampleProof2
import sequence.LinearCutExampleProof
import sequence.LinearEqExampleProof
import sequence.LinearExampleProof
import sequence.ProofSequence
import sequence.SquareDiagonalExampleProof
import sequence.SquareEdges2DimExampleProof
import sequence.SquareEdgesExampleProof
import sequence.SumExampleProof
import sequence.SumOfOnesExampleProof
import sequence.SumOfOnesF2ExampleProof
import sequence.SumOfOnesFExampleProof
import sequence.UniformAssociativity3ExampleProof

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
