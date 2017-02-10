package at.logic.gapt.proofsNew

case class DagProofBuilder[Jdg, Inf <: Inference[Jdg]]( stack: List[DagProof[Jdg, Inf]] = Nil ) {
  type Self = DagProofBuilder[Jdg, Inf]

  def c( proof: DagProof[Jdg, Inf] ): Self =
    copy( proof :: stack )

  def c( inf: Inf ): Self = {
    val n = inf.premises.size
    copy( DagProof( inf, stack.view.take( n ).reverse.toVector.ensuring( _.size == n ) ) :: stack.drop( n ) )
  }

  def u( inf: Jdg => Inf ): Self =
    c( inf( stack.head.conclusion ) )

  def b( inf: ( Jdg, Jdg ) => Inf ): Self =
    stack match {
      case ( right :: left :: _ ) => c( inf( left.conclusion, right.conclusion ) )
    }

  def qed: DagProof[Jdg, Inf] =
    stack match {
      case List( p ) => p
    }
}

