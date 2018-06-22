package gapt.proofs.ceres

import gapt.expr.{ Apps, _ }
import gapt.proofs.Context.{ ProofDefinitions, ProofNames }
import gapt.proofs.{ Context, MutableContext, Sequent }

object SchematicProjection {
  def apply( proofName: String, cut_occs: Sequent[Boolean] = Sequent[Boolean]() )( implicit ctx: MutableContext ): Unit = {
    val Proofs = ctx.get[ProofDefinitions].components.getOrElse( proofName, Set() )
    if ( Proofs.nonEmpty ) {
      val Proofname = ctx.get[ProofNames].names.get( proofName ).get
      val Apps( Const( n2, le, p ), lee ) = Proofname._1
      ctx += Const( proofName + "Proj", le, p )
      ctx += Context.ProofNameDeclaration( Apps( Const( proofName + "Proj", le, p ), lee ), Proofname._2 )
      Proofs.map( x => {
        val Apps( Const( n, l2, _ ), l ) = x.proofNameTerm
        //This is a stand in for the real projection code
        //not that proof name is wrong in that we do not have the characteristic
        //formula there yet
        ctx += Context.ProofDefinitionDeclaration( Apps( Const( proofName + "Proj", l2 ), l ), x.proof )
      } )
    }
  }
}
