package gapt.proofs

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
class ProofBuilder[+Proof](private val proofStack: List[Proof]) {

  /**
   * Pushes a proof onto the stack.
   *
   * @param proof An LKProof.
   * @return
   */
  def c[P >: Proof](proof: P): ProofBuilder[P] = new ProofBuilder(proof :: proofStack)

  /**
   * Applies a unary inference to the top element of the proof stack.
   *
   * @param inference A function LKProof => LKProof.
   * @return
   */
  def u[P >: Proof](inference: Proof => P): ProofBuilder[P] = proofStack match {
    case p :: rest => new ProofBuilder(inference(p) :: rest)
    case _         => throw new Exception("Cannot apply unary inference to empty stack.")
  }

  /**
   * Applies a binary inference to the top two elements of the proof stack.
   *
   * @param inference A function (LKProof, LKProof) => LKProof
   * @return
   */
  def b[P >: Proof](inference: (Proof, Proof) => P): ProofBuilder[P] = proofStack match {
    case Nil              => throw new Exception("Cannot apply binary inference to empty stack.")
    case _ :: Nil         => throw new Exception("Cannot apply binary inference to stack with only one element.")
    case p2 :: p1 :: rest => new ProofBuilder(inference(p1, p2) :: rest)
  }

  /**
   * Applies a ternary inference to the top three elements of the proof stack.
   *
   * @param inference A function (NDProof, NDProof, NDProof) => NDProof
   * @return
   */
  def t[P >: Proof](inference: (Proof, Proof, Proof) => P): ProofBuilder[P] = proofStack match {
    case Nil                    => throw new Exception("Cannot apply ternary inference to empty stack.")
    case _ :: Nil               => throw new Exception("Cannot apply ternary inference to stack with only one element.")
    case _ :: _ :: Nil          => throw new Exception("Cannot apply ternary inference to stack with only two elements.")
    case p3 :: p2 :: p1 :: rest => new ProofBuilder(inference(p1, p2, p3) :: rest)
  }

  /**
   * If there is exactly one proof on the stack, returns that proof.
   *
   * @return
   */
  def qed: Proof = proofStack match {
    case Nil      => throw new Exception("Proof stack is empty.")
    case p :: Nil => p
    case _        => throw new Exception("There is more than one proof on the stack.")
  }
}

object ProofBuilder extends ProofBuilder[Nothing](Nil)
