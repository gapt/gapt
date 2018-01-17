package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.ProofNames
import at.logic.gapt.proofs.{ Context, MutableContext, SequentConnector }

object CreateASchemaVersion extends LKVisitor[MutableContext] {
  override protected def recurse( p: LKProof, ctx: MutableContext ): ( LKProof, SequentConnector ) =
    p match {
      case proof @ InductionRule( casesI, form, typeTerm ) =>
        val newVarForDef = rename( Var( "x", typeTerm.ty ), freeVariables( proof.conclusion ) )
        val formNorm = BetaReduction.betaNormalize( form( newVarForDef ) ).asInstanceOf[Formula]
        val es = proof.endSequent.updated( proof.mainIndices.head, formNorm )
        val fv = freeVariables( es ).toList
        val name = Const( ctx.newNameGenerator.fresh( "Proof" ), FunctionType( typeTerm.ty, fv.map( _.ty ) ) )
        val proofName = Apps( name, fv )
        ctx += name
        ctx += Context.ProofNameDeclaration( proofName, es )
        casesI.foreach {
          case InductionCase( subproof, _, hy, _, con ) =>
            val sigma = syntacticMatching( formNorm, subproof.endSequent( con ) ).get
            val endSequentLeft = ctx.get[ProofNames].lookup( proofName ).getOrElse {
              throw new Exception( "Proof not defined" )
            }
            val finProof = hy.foldLeft( subproof )( ( outputProof, hypoth ) => {
              val outputSeq = endSequentLeft.replaceAt( con, subproof.endSequent( hypoth ) )
              val sigma2 = syntacticMatching( formNorm, subproof.endSequent( hypoth ) ).get
              ContractionMacroRule(
                CutRule(
                  ProofLink( sigma2( proofName ), outputSeq ),
                  outputSeq.indexOf( outputProof.endSequent( hypoth ) ),
                  outputProof, hypoth ),
                sigma( endSequentLeft ) )
            } )
            ArithmeticInductionToSchema( finProof, sigma( proofName ) )( ctx )
        }
        val newProofName = proofName.replace( proofName.find( newVarForDef ).head, typeTerm )
        withIdentitySequentConnector( ProofLink( newProofName, proof.endSequent ) )
      case _ => super.recurse( p, ctx )
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
