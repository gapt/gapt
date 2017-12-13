package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.natMaker
import at.logic.gapt.proofs.Context.{ ProofDefinition, ProofDefinitions, ProofNames }
import at.logic.gapt.proofs.lk.{ EigenVariablesLK, LKProof }
import at.logic.gapt.proofs.{ Context, Sequent }

//Idea behind the type is for each proof symbol we have a  Map,  which maps configurations to a
// a Struct  and the expression of the case of the inductive definition.
object SchematicStruct {
  def apply( topSym: String, cutConfig: Sequent[Boolean] = Sequent[Boolean](),
             foundCases: Set[( String, Sequent[Boolean] )] = Set[( String, Sequent[Boolean] )]() )( implicit ctx: Context ): Option[Map[CLS, ( Struct, Set[Var] )]] = {
    //If the context does not contain topSym then we cannot construct the struct and return None.
    if ( ctx.get[ProofDefinitions].components.keySet.contains( topSym ) ) {
      //If no cut config is provided we construct the default config
      val theActualConfig = if ( cutConfig.isEmpty ) {
        val ( _, theSeq ) = ctx.get[ProofNames].names.getOrElse( topSym, { throw new Exception( "Unhandled case: " + topSym ) } )
        theSeq.map( _ => false )
      } else cutConfig
      // We construct the struct for the given proof modulo the cutConfig
      val currentProofStruct: Map[CLS, ( Struct, Set[Var] )] =
        ctx.get[ProofDefinitions].components.getOrElse( topSym, Set() ).map {
          case ProofDefinition( placeHolder: Expr, _, assocProof: LKProof ) =>
            ( CLS( placeHolder, theActualConfig ),
              //need to write a predicate for cut ancestry
              ( StructCreators.extract( assocProof, theActualConfig )( { _ => true }, ctx ), EigenVariablesLK( assocProof ) ) )
        }.toMap
      //After constructing the struct we need to find all CLS terms
      val clauseSetDependencies = currentProofStruct.flatMap( e => {
        SchematicLeafs( e._2._1 ).filter {
          case CLS( Apps( Const( pf, _ ), _ ), ccon ) => !foundCases.contains( ( pf, ccon ) )
        }.map { case CLS( Apps( Const( pf, _ ), _ ), ccon ) => ( pf, ccon ) }
      } )
      // For each CLS term we compute the Struct and merge the results
      Some( clauseSetDependencies.map( x => SchematicStruct( x._1, x._2, foundCases ++ clauseSetDependencies - x +
        ( topSym -> theActualConfig ) ).getOrElse( { throw new Exception( "Struct could not be built " ) } ) ).foldLeft( Map[CLS, ( Struct, Set[Var] )]() )( ( x, y ) => x ++ y ) ++ currentProofStruct )
    } else None
  }
}
//Allows the construction of instances of schematic structs
object InstanceOfSchematicStruct {
  def apply(
    topSym:    CLS,
    sss:       Map[CLS, ( Struct, Set[Var] )],
    sigma:     Substitution,
    usedNames: Set[Var]                       = Set[Var]() )( implicit ctx: Context ): Struct = {
    val starterStruct = sss.getOrElse( topSym, { throw new Exception( "Not in Struct: " + topSym ) } )
    val CLS( Apps( _, lex ), _ ) = topSym
    // check if the Struct is empty or does not match sigma
    if ( freeVariables( lex ).forall( x => !sigma.domain.contains( x ) ) ) EmptyPlusJunction()
    else {
      //The following code regularizes the clause set
      val regularizedStruct = Set( usedNames.foldLeft( ( ( rename.awayFrom( usedNames ), usedNames ), starterStruct._1 ) )(
        ( reClause, nameVar ) => Set[Var]( Var( reClause._1._1.fresh( nameVar.name ), nameVar.ty ) ).map( newVar =>
          ( ( reClause._1._1, reClause._1._2 + newVar ), RenameVarsInStruct( reClause._2, Map( ( nameVar, newVar ) ) ) ) ).head ) ).map( x => ( x._1._2, x._2 ) ).head
      //we now unfold the dependencies
      InstantiateStruct( regularizedStruct._2, sigma, if ( freeVariables( lex.head ).size == 1 ) freeVariables( lex.head ).head
      else Var( "", TBase( "nat" ) ), sss, usedNames ++ regularizedStruct._1 )
    }
  }
}
object RenameVarsInStruct extends StructVisitor[Struct, ( Var, Var )] {
  def apply( theStruct: Struct, renamings: Map[Var, Var] ): Struct = {
    val Transform = StructTransformer[Struct, ( Var, Var )](
      aF, { ( x, y, _ ) => Plus( x, y ) }, EmptyPlusJunction(), { ( x, y, _ ) => Times( x, y ) },
      EmptyTimesJunction(), { ( x, _ ) => Dual( x ) }, cF )
    renamings.foldLeft( theStruct )( ( x, y ) => recurse( x, Transform, ( y._1, y._2 ) ) )
  }
  def aF( f: Formula, vars: ( Var, Var ) ): Struct = A( TermReplacement( f, vars._1, vars._2 ) )
  def cF( pn: Expr, cc: Sequent[Boolean], vars: ( Var, Var ) ): Struct = CLS( TermReplacement( pn, vars._1, vars._2 ), cc )

}
object InstantiateStruct extends StructVisitor[Struct, ( Substitution, Var, Map[CLS, ( Struct, Set[Var] )], Set[Var] )] {
  def apply( theStruct: Struct, sigma: Substitution, param: Var,
             sss:       Map[CLS, ( Struct, Set[Var] )],
             usedNames: Set[Var] )( implicit ctx: Context ): Struct = {
    val Transform = StructTransformer[Struct, ( Substitution, Var, Map[CLS, ( Struct, Set[Var] )], Set[Var] )](
      aF, { ( x, y, _ ) => Plus( x, y ) }, EmptyPlusJunction(), { ( x, y, _ ) => Times( x, y ) },
      EmptyTimesJunction(), { ( x, _ ) => Dual( x ) }, cF )
    recurse( theStruct, Transform, ( sigma, param, sss, usedNames ) )
  }
  def aF( f: Formula, info: ( Substitution, Var, Map[CLS, ( Struct, Set[Var] )], Set[Var] ) )( implicit ctx: Context ): Struct = {
    val ( sigma, _, _, _ ) = info
    A( sigma( sigma.domain.foldLeft( f )( ( subForm, varSig ) =>
      ( if ( varSig.ty.equals( TBase( "nat" ) ) ) subForm.find( natMaker( 1, varSig ) )
      else subForm.find( varSig ) ).foldLeft( subForm )( ( nRepl, curPos ) => nRepl.replace( curPos, varSig ) ) ) ) )
  }
  def cF( pn: Expr, cc: Sequent[Boolean], info: ( Substitution, Var, Map[CLS, ( Struct, Set[Var] )], Set[Var] ) )( implicit ctx: Context ): Struct = {
    val ( sigma, param, sss, usedNames ) = info
    val Apps( Const( name, _ ), vs ) = pn
    val newVs = vs.map( f => sigma( sigma.domain.foldLeft( f )( ( subform, varsig ) =>
      if ( varsig.ty.equals( TBase( "nat" ) ) )
        subform.find( natMaker( 1, varsig ) ).foldLeft( subform )( ( nrepl, curpos ) => ctx.get[ProofNames].names.get( name ) match {
        case Some( proofName ) =>
          val Apps( _, lsymPN ) = proofName._1
          if ( param.equals( lsymPN.head ) ) nrepl else if ( varsig.equals( param ) ) nrepl.replace( curpos, varsig ) else nrepl
        case None => nrepl
      } )
      else subform ) ) )
    val suc = ctx.get[Context.Constants].constants.getOrElse( "s", { throw new Exception( "nat not defined" ) } )
    val zero = ctx.get[Context.Constants].constants.getOrElse( "0", { throw new Exception( "nat not defined" ) } )
    val CLS( Apps( n, vs2 ), ccc ) = sss.keySet.find {
      case CLS( Apps( Const( n2, _ ), vs2 ), cc2 ) =>
        n2.matches( name ) && cc2.equals( cc ) && ( ( !sigma( vs.head ).equals( zero ) && vs2.head.contains( suc ) ) || ( vs2.head.equals( zero ) && sigma( vs.head ).equals( zero ) ) )
    }.getOrElse( throw new Exception( "??????????" ) )
    val newSigma = vs2.zip( newVs ).map {
      case ( one, two ) => //We know this is at most size one for nat
        freeVariables( one ).map( x => one.find( x ) ).foldLeft( List[HOLPosition]() )( ( fin, ll ) => fin ++ ll ).headOption match {
          case Some( pos ) => ( one.get( pos ).getOrElse( one ), two.get( pos ).getOrElse( two ) )
          case None        => ( one, two )
        }
    }.foldLeft( Substitution() )( ( sub, pair ) => if ( freeVariables( pair._1 ).isEmpty ) sub else sub.compose( Substitution( pair._1.asInstanceOf[Var], pair._2 ) ) )
    InstanceOfSchematicStruct( CLS( Apps( n, vs2 ), ccc ), sss, newSigma, usedNames )
  }
}