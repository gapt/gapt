package gapt.proofs.context.update

import gapt.expr.Abs
import gapt.expr.Apps
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.VarOrConst
import gapt.expr.formula.Eq
import gapt.expr.formula.Formula
import gapt.expr.ty.FunctionType
import gapt.expr.ty.TBase
import gapt.expr.ty.Ti
import gapt.expr.util.freeVariables
import gapt.proofs.HOLSequent
import gapt.proofs.context.Context
import gapt.proofs.context.State
import gapt.proofs.context.update.{ ConstantDeclaration => ConstDecl }

/**
 * Update of a context.
 *
 * An update stores (potentially multiple) modifications to a [[Context]].
 * It is represented by a function that takes a [[Context]], and returns the modified [[State]].
 */
trait Update {
  /**
   * Applies the modifications of this update to ctx.
   *
   * Throws an exception if the modifications are invalid (for example if we would redefine a constant).
   */
  def apply( ctx: Context ): State
}
object Update {
  implicit def fromSort( ty: TBase ): Update = Sort( ty )
  implicit def fromConst( const: Const ): Update = ConstDecl( const )
  implicit def fromDefn( defn: ( String, Expr ) ): Update =
    Definition( Const( defn._1, defn._2.ty ), defn._2 )
  implicit def fromDefnEq( eq: Formula ): Update = eq match {
    case Eq( Apps( VarOrConst( name, ty, ps ), vars ), by ) =>
      Definition( Const( name, ty, ps ), Abs.Block( vars.map( _.asInstanceOf[Var] ), by ) )
  }
  implicit def fromAxiom( axiom: ( String, HOLSequent ) ): Update = {
    val fvs = freeVariables( axiom._2 ).toVector.sortBy( _.toString )
    val name = Const( axiom._1, FunctionType( Ti, fvs.map( _.ty ) ) )( fvs )
    ProofNameDeclaration( name, axiom._2 )
  }
}