package gapt.provers.viper

import gapt.expr.{ Const, Expr }
import gapt.expr.formula.{ Formula, Neg }
import gapt.expr.ty.{ TArr, Ty }
import gapt.proofs.Sequent
import gapt.proofs.context.Context

package object spin {

  // Replaces x with e in f.
  def replaceExpr( f: Formula, x: Expr, e: Expr ): Formula =
    f.find( x ).foldLeft( f )( ( f, pos ) => f.replace( pos, e ) )

  def negate( f: Formula ): Formula = f match {
    case Neg( g ) => g
    case _        => Neg( f )
  }

  def resType( ty: Ty ): Ty =
    ty match {
      case TArr( _, t ) => resType( t )
      case _            => ty
    }

  // Is c a constructor
  def isConstructor( c: Const )( implicit ctx: Context ): Boolean =
    ctx.getConstructors( resType( c.ty ) ) match {
      case None            => false
      case Some( constrs ) => constrs.contains( c )
    }

  def lambdaType( t: String ): Boolean = t.matches( "fun[0-9]+" )

  private[spin] implicit def labeledSequentToHOLSequent( sequent: Sequent[( String, Formula )] ): Sequent[Formula] =
    sequent map { case ( _, f ) => f }
}
