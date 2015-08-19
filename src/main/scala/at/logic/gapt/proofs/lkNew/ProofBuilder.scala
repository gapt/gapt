package at.logic.gapt.proofs.lkNew

/**
 * Created by sebastian on 8/15/15.
 */
object ProofBuilder {
  def apply( inferences: InferenceFunction* ): Seq[LKProof] = {
    ( Seq.empty[LKProof] /: inferences ) { ( acc, i ) => i.fun( acc ) }
  }

  abstract class InferenceFunction {
    def fun( list: Seq[LKProof] ): Seq[LKProof]
  }

  implicit class ConstantProofFunction( proof: LKProof ) extends InferenceFunction {
    def fun( list: Seq[LKProof] ): Seq[LKProof] = proof +: list
  }

  implicit class UnaryInferenceFunction( inference: LKProof => LKProof ) extends InferenceFunction {
    def fun( list: Seq[LKProof] ): Seq[LKProof] = list match {

      case Nil       => throw new Exception( "Cannot apply unary inference to empty list." )
      case p :: rest => inference( p ) :: rest
    }
  }

  implicit class BinaryInferenceFunction( inference: ( LKProof, LKProof ) => LKProof ) extends InferenceFunction {
    def fun( list: Seq[LKProof] ): Seq[LKProof] = list match {
      case Nil              => throw new Exception( "Cannot apply binary inference to empty list." )
      case _ :: Nil         => throw new Exception( "Cannot apply binary inference list with only one element." )
      case p1 :: p2 :: rest => inference( p2, p1 ) +: rest
    }
  }
}

