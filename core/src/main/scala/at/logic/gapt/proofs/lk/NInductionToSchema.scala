package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.{ Apps, Const, Expr, Formula, TArr, TBase, Ty, Var, freeVariables, rename }
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
    val result = proof.subProofs.foldLeft( List[( Expr, LKProof )]() )( ( x, y ) => y match {
      case InductionRule( _, _, _ ) =>
        val es = y.endSequent
        val fv = freeVariablesLK( y ).toList
        val ptype = fv.foldLeft( TBase( "nat" ).asInstanceOf[Ty] )( ( x, vc ) => TArr( vc.ty, x ) )
        val name = Const( newNames.fresh( "P" ), ptype )
        val proofname = Apps( name, fv )
        ctx += name
        ctx += Context.ProofNameDeclaration( proofname, es )
        ( proofname, y ) :: x
      case _ => x
    } )
    val resProof: LKProof = CreateASchemaVersion( proof, ( result.unzip._1, ctx ) )
    if ( ctx.get[ProofNames].lookup( pe ).isEmpty ) {
      ctx += Const( nameT, tpp )
      ctx += Context.ProofNameDeclaration( pe, resProof.endSequent )
    }
    ctx += Context.ProofDefinitionDeclaration( pe, resProof )
    result.foreach( x => {
      val Apps( Const( name, tp ), vars ) = x._1
      val InductionRule( cases, _, term ) = x._2
      cases.foreach( y => {
        val InductionCase( p, _, hy, ev, _ ) = y
        val suc = ctx.get[Context.Constants].constants.getOrElse( "s", {
          throw new Exception( "nat not defined" )
        } )
        val zero = ctx.get[Context.Constants].constants.getOrElse( "0", {
          throw new Exception( "nat not defined" )
        } )
        val newvar = if ( ev.isEmpty ) vars.map( x => if ( x.equals( term ) ) zero else x )
        else vars.map( x => if ( x.equals( term ) ) Apps( suc, ev.head ) else x )
        val endSequentLeft = ctx.get[ProofNames].lookup( x._1 ).getOrElse( {
          throw new Exception( "Proof not defined" )
        } )
        val finproof = if ( ev.nonEmpty ) {
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
          val cutproof = CutRule( ProofLink( newex, newseq ), newseq.indexOf( p.endSequent( hy.head ) ), p, hy.head )

          val target = Sequent(
            endSequentLeft.antecedent.map( e =>
              e.find( term ).foldLeft( e )( ( z, w ) => {
                if ( freeVariables( e ).contains( term.asInstanceOf[Var] ) )
                  z.replace( w, Apps( suc, ev.head ) )
                else z
              } ) ),
            endSequentLeft.succedent.map( e =>
              e.find( term ).foldLeft( e )( ( z, w ) => {
                if ( freeVariables( e ).contains( term.asInstanceOf[Var] ) )
                  z.replace( w, Apps( suc, ev.head ) )
                else z
              } ) ) )
          ContractionMacroRule( cutproof, target )
        } else {
          val newante = endSequentLeft.antecedent.foldLeft( Set[Formula]() )( ( r, t ) => {
            if ( p.endSequent.indexOfOption( t ).isEmpty && ( !t.contains( term ) || !freeVariables( t ).contains( term.asInstanceOf[Var] ) ) ) r + t
            else if ( t.contains( term ) || !freeVariables( t ).contains( term.asInstanceOf[Var] ) ) r
            else r
          } )
          val newsuc = endSequentLeft.succedent.foldLeft( Set[Formula]() )( ( r, t ) => {
            if ( p.endSequent.indexOfOption( t ).isEmpty && ( !t.contains( term ) || !freeVariables( t ).contains( term.asInstanceOf[Var] ) ) ) r + t
            else if ( t.contains( term ) || !freeVariables( t ).contains( term.asInstanceOf[Var] ) ) r
            else r
          } )
          val pp = WeakeningLeftMacroRule( p, newante.toSeq )
          WeakeningRightMacroRule( pp, newsuc.toSeq )
        }
        ArithmeticInductionToSchema( finproof, Apps( Const( name, tp ), newvar ) )( ctx )
      } )
    } )
  }

}
