package at.logic.gapt.proofs.lk

/**
 * Created by sebastian on 8/15/15.
 */

/**
 * Class for convenient construction of proofs.
 * Allows you to write proofs post-order style (à la Bussproofs). Example:
 * <pre>
 * (ProofBuilder
 * c LogicalAxiom(A)
 * c LogicalAxiom(B)
 * u (WeakeningLeftRule(_, C))
 * b (AndRightRule(_,_, And(A, B))
 * qed)
 * </pre>
 * The constructor is private, so the only way to instantiate this class is by using the ProofBuilder object.
 * This means that the stack will always be empty in the beginning.
 *
 * @param proofStack
 */
class ProofBuilder private ( private val proofStack: Seq[LKProof] ) {

  /**
   * Pushes a proof onto the stack.
   *
   * @param proof An LKProof.
   * @return
   */
  def c( proof: LKProof ) = new ProofBuilder( proof +: proofStack )

  /**
   * Applies a unary inference to the top element of the proof stack.
   *
   * @param inference A function LKProof => LKProof.
   * @return
   */
  def u( inference: LKProof => LKProof ) = proofStack match {
    case p +: rest => new ProofBuilder( inference( proofStack.head ) +: proofStack.tail )
    case _         => throw new Exception( "Cannot apply unary inference to empty stack." )
  }

  /**
   * Applies a binary inference to the top two elements of the proof stack.
   *
   * @param inference A function (LKProof, LKProof) => LKProof
   * @return
   */
  def b( inference: ( LKProof, LKProof ) => LKProof ) = proofStack match {
    case Seq()            => throw new Exception( "Cannot apply binary inference to empty stack." )
    case p +: Seq()       => throw new Exception( "Cannot apply binary inference to stack with only one element." )
    case p2 +: p1 +: rest => new ProofBuilder( inference( p1, p2 ) +: rest )
  }

  /**
   * If there is exactly one proof on the stack, returns that proof.
   *
   * @return
   */
  def qed = proofStack match {
    case Seq()      => throw new Exception( "Proof stack is empty." )
    case p +: Seq() => p
    case _          => throw new Exception( "There is more than one proof on the stack." )
  }
}

object ProofBuilder extends ProofBuilder( Seq() )