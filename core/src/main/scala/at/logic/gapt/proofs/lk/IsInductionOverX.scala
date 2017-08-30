package at.logic.gapt.proofs.lk
import at.logic.gapt.proofs.Context.InductiveType

/**
  * Using the LKPropVisitor check is all the inductions in the given
  * proof are of the correct inductive type.
  * @tparam arg The inductive type.
  */object IsInductionOverX {
  def apply( proof: LKProof, arg: InductiveType ): Boolean = Propchecker( proof, arg )

  private object Propchecker extends LKPropVisitor[InductiveType] {
    override def visitInduction( proof: InductionRule, otherArg: InductiveType ): Boolean =
      if ( proof.indTy.toString.compareTo( otherArg.ty.name ) == 0 ) joinProp( proof, otherArg )
      else false
  }
}
