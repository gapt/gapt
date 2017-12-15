package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.ProofNames
import at.logic.gapt.proofs.{Context, MutableContext, Sequent, SequentConnector}

object CreateASchemaVersion extends LKVisitor[( List[(Expr,Var)], Context )] {
  override protected def recurse( proof: LKProof, arg: ( List[(Expr,Var)], Context ) ): ( LKProof, SequentConnector ) = {
    proof match {
      case InductionRule( _, _, t ) =>
        val thepairs = arg._1.map( x => ( x, arg._2.get[ProofNames].lookup( x._1 ).getOrElse( Sequent() ) ) )
        val result = thepairs.foldLeft( thepairs.head )( ( x, y ) =>{
          val es = proof.endSequent.map(f=> TermReplacement(f,t,y._1._2))
          if ( es.equals( y._2 ) ) y else x
        })
        withIdentitySequentConnector( ProofLink( result._1._1, proof.endSequent ) )
      case _ => super.recurse( proof, arg )
    }
  }
}
object ArithmeticInductionToSchema {
  def apply( proof: LKProof, pe: Expr )( implicit ctx: MutableContext ): Unit = {
    val Apps( Const( nameT, tpp ), _ ) = pe
    val newNames = ctx.newNameGenerator
    val subProofNames = proof.subProofs.collect{  case p @ InductionRule( casesI, form, typeTerm ) =>
        val newVarForDef =  typeTerm.asInstanceOf[Var] //Var(newNames.fresh( "x" ),typeTerm.ty)
        val es = p.endSequent.map(f=> TermReplacement(f,typeTerm,newVarForDef))
        val newForm = TermReplacement(form,typeTerm,newVarForDef).asInstanceOf[Abs]
        val fv = newVarForDef :: freeVariables( form ).toList
        val name = Const( newNames.fresh( "P" ),  FunctionType( typeTerm.ty, fv.map( _.ty ) ) )
        val proofname = Apps( name, fv )
        ctx += name
        ctx += Context.ProofNameDeclaration( proofname,es)
        ( (proofname,newVarForDef), ( newForm, InductionRule( casesI, newForm, newVarForDef ) ) )
    }.toList
    val resProof: LKProof = CreateASchemaVersion( proof, ( subProofNames.unzip._1, ctx ) )
    if ( ctx.get[ProofNames].lookup( pe ).isEmpty ) {
      ctx += Const( nameT, tpp )
      ctx += Context.ProofNameDeclaration( pe, resProof.endSequent )
    }
    ctx += Context.ProofDefinitionDeclaration( pe, resProof )
    subProofNames.foreach{ case ((proofname,_),(Abs( _, form ), InductionRule( casesI, _, term ) )) =>
      casesI.foreach{ case  InductionCase( p, _, hy, ev, con ) =>
        val sigma = syntacticMatching( form, p.endSequent( con ) ).get
        val endSequentLeft = ctx.get[ProofNames].lookup( proofname).getOrElse( { throw new Exception( "Proof not defined" ) } )
        val finProof = if ( ev.nonEmpty ) {
          val newseq = endSequentLeft.map( e => e.find( term ).foldLeft( e )( ( z, w ) => {
                if ( freeVariables( e ).contains( term.asInstanceOf[Var] ) ) z.replace( w, ev.head ) else z} ) )
          val newex = proofname.find( term ).foldLeft( proofname )( ( z, w ) => { z.replace( w, ev.head ) } )
          ContractionMacroRule( CutRule( ProofLink( newex, newseq ), newseq.indexOf( p.endSequent( hy.head ) ), p, hy.head ), sigma( endSequentLeft ) )
        } else {
          val newante = endSequentLeft.antecedent.foldLeft( List[Formula]() )( ( r, t ) => {
            if ( p.endSequent.indexOfOption( t ).isEmpty && ( !t.contains( term ) || !freeVariables( t ).contains( term.asInstanceOf[Var] ) ) ) t :: r
            else r
          } )
          val newsuc = endSequentLeft.succedent.filterNot( t => p.endSequent.indexOfOption( t ).isEmpty && ( !t.contains( term ) || !freeVariables( t ).contains( term.asInstanceOf[Var] ) ) )
          WeakeningRightMacroRule( WeakeningLeftMacroRule( p, newante ), newsuc )
        }
        ArithmeticInductionToSchema( finProof, sigma( proofname ) )( ctx )
       }
    }
  }

}
