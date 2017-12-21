package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.{ ProofDefinition, ProofDefinitions, ProofNames }
import at.logic.gapt.proofs.lk.{ EigenVariablesLK, LKProof }
import at.logic.gapt.proofs.{ Context, Sequent }

//Idea behind the type is for each proof symbol we have a  Map,  which maps configurations to a
// a Struct  and the expression of the case of the inductive definition.
object SchematicStruct {
  def apply( topSym: String, cutConfig: Sequent[Boolean] = Sequent[Boolean](),
             foundCases: Set[( String, Sequent[Boolean] )] = Set[( String, Sequent[Boolean] )]() )(
    implicit
    ctx: Context ): Option[Map[CLS, ( Struct, Set[Var] )]] = {
    //If the context does not contain topSym then we cannot construct the struct and return None.
    if ( ctx.get[ProofDefinitions].components.keySet.contains( topSym ) ) {
      //If no cut config is provided we construct the default config
      val theActualConfig = if ( cutConfig.isEmpty ) {
        val ( _, theSeq ) = ctx.get[ProofNames].names.getOrElse(
          topSym,
          throw new Exception( "Unhandled case: " + topSym ) )
        theSeq.map( _ => false )
      } else cutConfig
      // We construct the struct for the given proof modulo the cutConfig
      val currentProofStruct: Map[CLS, ( Struct, Set[Var] )] =
        ctx.get[ProofDefinitions].components.getOrElse( topSym, Set() ).map {
          case ProofDefinition( placeHolder: Expr, _, assocProof: LKProof ) =>
            ( CLS( placeHolder, theActualConfig ),
              (
                StructCreators.extract( assocProof, theActualConfig )( _ => true, ctx ),
                EigenVariablesLK( assocProof ) ) )
        }.toMap
      //After constructing the struct we need to find all CLS terms
      val clauseSetDependencies = currentProofStruct.flatMap( e => {
        SchematicLeafs( e._2._1 ).filter {
          case CLS( Apps( Const( pf, _ ), _ ), ccon ) => !foundCases.contains( ( pf, ccon ) )
        }.map { case CLS( Apps( Const( pf, _ ), _ ), ccon ) => ( pf, ccon ) }
      } )
      // For each CLS term we compute the Struct and merge the results
      Some( clauseSetDependencies.flatMap( x =>
        SchematicStruct( x._1, x._2, foundCases ++ clauseSetDependencies - x +
          ( topSym -> theActualConfig ) ).getOrElse {
          throw new Exception( "Struct could not be built " )
        } ) ++ currentProofStruct )
    } else None
  }
}
//Allows the construction of instances of schematic structs
object InstanceOfSchematicStruct {
  def apply( topSym: CLS, sss: Map[CLS, ( Struct, Set[Var] )], usedNames: Set[Var] = Set[Var]() )(
    implicit
    ctx: Context ): Struct = {
    val ( starterStruct, sigma ) = ( for {
      ( sssCls, sssStruct ) <- sss
      if sssCls.config == topSym.config
      sigma <- syntacticMatching( sssCls.proof, topSym.proof )
    } yield ( sssStruct, sigma ) ).head
    val renamedStruct = Set( usedNames.foldLeft( ( ( rename.awayFrom( usedNames ), usedNames ), starterStruct._1 ) )(
      ( reClause, nameVar ) => Set[Var]( Var( reClause._1._1.fresh( nameVar.name ), nameVar.ty ) ).map( newVar =>
        ( ( reClause._1._1, reClause._1._2 + newVar ),
          TermReplacement( reClause._2, Map( ( nameVar, newVar ) ) ) ) ).head ) ).map( x => ( x._1._2, x._2 ) ).head
    InstantiateStruct( renamedStruct._2, sigma, sss, usedNames ++ renamedStruct._1 )
  }
}
object InstantiateStruct extends StructVisitor[Struct, ( Substitution, Map[CLS, ( Struct, Set[Var] )], Set[Var] )] {
  def apply( theStruct: Struct, sigma: Substitution,
             sss: Map[CLS, ( Struct, Set[Var] )], usedNames: Set[Var] )( implicit ctx: Context ): Struct = {
    val Transform = StructTransformer[Struct, ( Substitution, Map[CLS, ( Struct, Set[Var] )], Set[Var] )](
      aF, { ( x, y, _ ) => Plus( x, y ) }, EmptyPlusJunction(), { ( x, y, _ ) => Times( x, y ) },
      EmptyTimesJunction(), { ( x, _ ) => Dual( x ) }, cF )
    recurse( theStruct, Transform, ( sigma, sss, usedNames ) )
  }
  def aF( f: Formula, info: ( Substitution, Map[CLS, ( Struct, Set[Var] )], Set[Var] ) )(
    implicit
    ctx: Context ): Struct =
    A( info._1( f ) )
  def cF( pn: Expr, cc: Sequent[Boolean], info: ( Substitution, Map[CLS, ( Struct, Set[Var] )], Set[Var] ) )(
    implicit
    ctx: Context ): Struct =
    InstanceOfSchematicStruct( CLS( info._1( pn ), cc ), info._2, info._3 )
}