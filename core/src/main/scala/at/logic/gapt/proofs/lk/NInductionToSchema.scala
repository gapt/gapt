package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.ProofNames
import at.logic.gapt.proofs.{ Context, MutableContext, SequentConnector }

object CreateASchemaVersion extends LKVisitor[MutableContext] {
  override protected def recurse( p: LKProof, ctx: MutableContext ): ( LKProof, SequentConnector ) = {
    val newNames = ctx.newNameGenerator
    p match {
      case proof@InductionRule( casesI, form, typeTerm  ) =>
        val formNorm =  BetaReduction.betaNormalize(form( typeTerm ))
        val newVarForDef = Var( newNames.fresh( "x" ), typeTerm.ty )
        val es = proof.endSequent.map( f => typeTerm match {
          case v@ Var(_,_) => if(freeVariables(f).contains(v)) TermReplacement( f, typeTerm, newVarForDef ) else f
          case _ => TermReplacement( f, typeTerm, newVarForDef )
        })
        val fv = freeVariables( TermReplacement( formNorm, typeTerm, newVarForDef ) ).toList
        val name = Const( newNames.fresh( "Proof" ), FunctionType( typeTerm.ty, fv.map( _.ty ) ) )
        val proofName = Apps( name, fv )
        ctx += name
        ctx += Context.ProofNameDeclaration( proofName, es )
        casesI.foreach {
          case InductionCase( subproof, _, hy, _, con ) =>
            val sigma = syntacticMatching(formNorm , subproof.endSequent( con ) ).get
            val endSequentLeft = ctx.get[ProofNames].lookup( proofName ).getOrElse( { throw new Exception( "Proof not defined" ) } )
            val finProof = if ( hy.nonEmpty ) hy.foldLeft( subproof )( ( outputProof, hypoth ) => {
              val outputSeq = sigma( endSequentLeft.replaceAt( con, subproof.endSequent( hypoth ) ) )
              ContractionMacroRule( CutRule( ProofLink( syntacticMatching( formNorm, subproof.endSequent( hypoth ) ).get( proofName ), outputSeq ), outputSeq.indexOf( outputProof.endSequent( hypoth ) ), outputProof, hypoth ), sigma( endSequentLeft ) )
            } )
            else {
              val newante = endSequentLeft.antecedent.filter( t => subproof.endSequent.indexOfOption( t ).isEmpty && ( !t.contains( typeTerm ) || !freeVariables( t ).contains( typeTerm.asInstanceOf[Var] ) ) )
              val newsuc = endSequentLeft.succedent.filterNot( t => subproof.endSequent.indexOfOption( t ).isEmpty && ( !t.contains( typeTerm ) || !freeVariables( t ).contains( typeTerm.asInstanceOf[Var] ) ) )
              WeakeningRightMacroRule( WeakeningLeftMacroRule( subproof, newante ), newsuc )
            }
            ArithmeticInductionToSchema( finProof, sigma( proofName ) )(ctx)
        }
        withIdentitySequentConnector(ProofLink( TermReplacement(proofName,newVarForDef,typeTerm), proof.endSequent ))
      case _ => super.recurse( p, ctx )
    }
  }
}
object ArithmeticInductionToSchema {
  def apply( proof: LKProof, pe: Expr )( implicit ctx: MutableContext ): Unit = {
    val Apps( Const( nameT, tpp ), _ ) = pe
    val resProof: LKProof = CreateASchemaVersion( proof, ctx )
    if ( ctx.get[ProofNames].lookup( pe ).isEmpty ) {
      ctx += Const( nameT, tpp )
      ctx += Context.ProofNameDeclaration( pe, resProof.endSequent )
    }
    ctx += Context.ProofDefinitionDeclaration( pe, resProof )
  }

}
