package gapt

import gapt.examples.sequence.FactorialFunctionEqualityExampleProof
import gapt.examples.sequence.FactorialFunctionEqualityExampleProof2
import gapt.examples.sequence.LinearCutExampleProof
import gapt.examples.sequence.LinearEqExampleProof
import gapt.examples.sequence.LinearExampleProof
import gapt.examples.sequence.ProofSequence
import gapt.examples.sequence.SquareDiagonalExampleProof
import gapt.examples.sequence.SquareEdges2DimExampleProof
import gapt.examples.sequence.SquareEdgesExampleProof
import gapt.examples.sequence.SumExampleProof
import gapt.examples.sequence.SumOfOnesExampleProof
import gapt.examples.sequence.SumOfOnesF2ExampleProof
import gapt.examples.sequence.SumOfOnesFExampleProof
import gapt.examples.sequence.UniformAssociativity3ExampleProof

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
