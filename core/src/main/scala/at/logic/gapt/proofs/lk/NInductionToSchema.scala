package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.{ Abs, Apps, Const, Expr, Formula, FunctionType, Var, freeVariables, rename, syntacticMatching }
import at.logic.gapt.proofs.Context.ProofNames
import at.logic.gapt.proofs.{ Context, MutableContext, Sequent, SequentConnector }
import at.logic.gapt.utils.NameGenerator

object CreateASchemaVersion extends LKVisitor[( List[Expr], Context )] {
  override protected def recurse( proof: LKProof, arg: ( List[Expr], Context ) ): ( LKProof, SequentConnector ) = {
    proof match {
      case InductionRule( _, _, _ ) =>
        val thepairs = arg._1.map( x => ( x, arg._2.get[ProofNames].lookup( x ).getOrElse( Sequent() ) ) )
        val result = thepairs.foldLeft( thepairs.head )( ( x, y ) =>
          if ( proof.endSequent.equals( y._2 ) ) y else x )
        withIdentitySequentConnector( ProofLink( result._1, proof.endSequent ) )
      case _ => super.recurse( proof, arg )
    }
  }
}
object ArithmeticInductionToSchema {
  def apply( proof: LKProof, pe: Expr )( implicit ctx: MutableContext ): Unit = {
    val Apps( Const( nameT, tpp ), _ ) = pe
    val newNames: NameGenerator = rename.awayFrom(
      ctx.get[ProofNames].names.keySet.map( x => {
        val Apps( Const( na, t ), _ ) = ctx.get[ProofNames].names.getOrElse( x, {
          throw new Exception( "not defined" )
        } )._1
        Const( na, t )
      } ) + Const( nameT, tpp ) )
    val result = proof.subProofs.foldLeft( List[( Expr, ( Abs, LKProof ) )]() )( ( x, y ) => y match {
      case InductionRule( _, form, typeTerm ) =>
        val es = y.endSequent
        val fv = typeTerm :: freeVariables( form ).toList
        val ptype = FunctionType( typeTerm.ty, fv.map( _.ty ) )
        val name = Const( newNames.fresh( "P" ), ptype )
        val proofname = Apps( name, fv )
        ctx += name
        ctx += Context.ProofNameDeclaration( proofname, es )
        ( proofname, ( form, y ) ) :: x
      case _ => x
    } )
    val resProof: LKProof = CreateASchemaVersion( proof, ( result.unzip._1, ctx ) )
    if ( ctx.get[ProofNames].lookup( pe ).isEmpty ) {
      ctx += Const( nameT, tpp )
      ctx += Context.ProofNameDeclaration( pe, resProof.endSequent )
    }
    ctx += Context.ProofDefinitionDeclaration( pe, resProof )
    result.foreach( x => {
      val Abs( _, form ) = x._2._1
      val InductionRule( cases, _, term ) = x._2._2
      cases.foreach( y => {
        val InductionCase( p, _, hy, ev, con ) = y
        val sigma = syntacticMatching( form, p.endSequent( con ) ).get
        val endSequentLeft = ctx.get[ProofNames].lookup( x._1 ).getOrElse( { throw new Exception( "Proof not defined" ) } )
        val finProof = if ( ev.nonEmpty ) {
          //*********************************************************************************************
          val newseq = Sequent(
            endSequentLeft.antecedent.map( e =>
              e.find( term ).foldLeft( e )( ( z, w ) => {
                if ( freeVariables( e ).contains( term.asInstanceOf[Var] ) )
                  z.replace( w, ev.head )
                else z
              } ) ),
            endSequentLeft.succedent.map( e =>
              e.find( term ).foldLeft( e )( ( z, w ) => {
                if ( freeVariables( e ).contains( term.asInstanceOf[Var] ) )
                  z.replace( w, ev.head )
                else z
              } ) ) )
          val newex = x._1.find( term ).foldLeft( x._1 )( ( z, w ) => { z.replace( w, ev.head ) } )
          //*********************************************************************************************
          ContractionMacroRule( CutRule( ProofLink( newex, newseq ), newseq.indexOf( p.endSequent( hy.head ) ), p, hy.head ), sigma( endSequentLeft ) )
        } else {
          val newante = endSequentLeft.antecedent.foldLeft( List[Formula]() )( ( r, t ) => {
            if ( p.endSequent.indexOfOption( t ).isEmpty && ( !t.contains( term ) || !freeVariables( t ).contains( term.asInstanceOf[Var] ) ) ) t :: r
            else r
          } )
          val newsuc = endSequentLeft.succedent.filterNot( t => p.endSequent.indexOfOption( t ).isEmpty && ( !t.contains( term ) || !freeVariables( t ).contains( term.asInstanceOf[Var] ) ) )
          WeakeningRightMacroRule( WeakeningLeftMacroRule( p, newante ), newsuc )
        }
        ArithmeticInductionToSchema( finProof, sigma( x._1 ) )( ctx )
      } )
    } )
  }

}
