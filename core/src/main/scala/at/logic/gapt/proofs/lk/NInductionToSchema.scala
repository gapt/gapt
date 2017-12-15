package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.ProofNames
import at.logic.gapt.proofs.{Context, MutableContext, Sequent, SequentConnector}

object CreateASchemaVersion extends LKVisitor[( List[Expr], Context )] {
  override protected def recurse( proof: LKProof, arg: ( List[Expr], Context ) ): ( LKProof, SequentConnector ) = {
    proof match {
      case InductionRule( _, _, _ ) =>
        val thepairs = arg._1.map( x => ( x, arg._2.get[ProofNames].lookup( x ).getOrElse( Sequent() ) ) )
        val result = thepairs.foldLeft( thepairs.head )( ( x, y ) =>if ( proof.endSequent.equals( y._2 ) ) y else x)
        withIdentitySequentConnector( ProofLink( result._1, proof.endSequent ) )
      case _ => super.recurse( proof, arg )
    }
  }
}
object ArithmeticInductionToSchema {
  def apply( proof: LKProof, pe: Expr )( implicit ctx: MutableContext ): Unit = {
    val Apps( Const( nameT, tpp ), _ ) = pe
    val newNames = ctx.newNameGenerator
    val subProofNames = proof.subProofs.collect{  case p @ InductionRule( casesI, form, typeTerm ) =>
        val newVarForDef =  Var(newNames.fresh( "x" ),typeTerm.ty)
        val es = p.endSequent.map(f=> TermReplacement(f,typeTerm,newVarForDef))
        val fv =  freeVariables( TermReplacement(form(typeTerm),typeTerm,newVarForDef) ).toList
        val name = Const( newNames.fresh( "Proof" ),  FunctionType(typeTerm.ty, fv.map( _.ty ) ) )
        val proofName = Apps( name, fv )
        ctx += name
        ctx += Context.ProofNameDeclaration( proofName,es)
        ( proofName, ( form, InductionRule( casesI, form, typeTerm ) ) )
    }.toList
    val resProof: LKProof = CreateASchemaVersion( proof, ( subProofNames.unzip._1, ctx ) )
    if ( ctx.get[ProofNames].lookup( pe ).isEmpty ) {
      ctx += Const( nameT, tpp )
      ctx += Context.ProofNameDeclaration( pe, resProof.endSequent )
    }
    println(resProof)
    ctx += Context.ProofDefinitionDeclaration( pe, resProof )
    subProofNames.foreach{ case (proofName,(Abs( _, form ), InductionRule( casesI, _, term ) )) =>
      casesI.foreach{ case  InductionCase( p, _, hy, _, con ) =>
        println(p.endSequent(hy))
        val sigma = syntacticMatching(form, p.endSequent(con)).get
        val endSequentLeft = ctx.get[ProofNames].lookup(proofName).getOrElse({throw new Exception("Proof not defined")})
        val finProof = if(hy.nonEmpty)  hy.foldLeft(p)((outputProof, hypoth)  => {
            val outputSeq = sigma(endSequentLeft.replaceAt(con,p.endSequent(hypoth)))
            ContractionMacroRule(CutRule(ProofLink(syntacticMatching(form, p.endSequent(hypoth)).get(proofName), outputSeq), outputSeq.indexOf(outputProof.endSequent(hypoth)), outputProof, hypoth), sigma(endSequentLeft))
        })
        else{
          val newante = endSequentLeft.antecedent.filter(t => p.endSequent.indexOfOption(t).isEmpty && (!t.contains(term) || !freeVariables(t).contains(term.asInstanceOf[Var])))
          val newsuc = endSequentLeft.succedent.filterNot(t => p.endSequent.indexOfOption(t).isEmpty && (!t.contains(term) || !freeVariables(t).contains(term.asInstanceOf[Var])))
          WeakeningRightMacroRule(WeakeningLeftMacroRule(p, newante), newsuc)
        }
        ArithmeticInductionToSchema( finProof, sigma( proofName ) )( ctx )

       }

    }
  }

}
