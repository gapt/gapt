package gapt.expr.util

import gapt.expr.Abs
import gapt.expr.Apps
import gapt.expr.Expr
import gapt.expr.FunctionType
import gapt.expr.Var
import gapt.utils.NameGenerator

/**
 * If t = λx₁...λxₘ(y u₁ ... uₚ) is a normal term of type T₁ → ... → Tₙ → U, with
 * U atomic and m ≤ n, then its long normal form is the term
 *
 * λx₁...λxₘλxₘ₊₁...λxₙ(y u₁'... uₚ' xₘ₊₁' ... xₙ'),
 *
 * where uᵢ' is the long normal form of uᵢ and xⱼ' is the long normal form of xⱼ.
 *
 * Implemented according to Definition 2.25, Higher-Order Unification and
 * Matching by Gilles Dowek.
 */
object longNormalForm {

  /**
   * Computes the long normal form.
   *
   * @param term A term.
   * @return The long normal form of `term`. Note that η-expansion is applied
   * only to expressions in β-normal form.
   */
  def apply( e: Expr ): Expr =
    e match {
      case Abs( v, e_ ) => Abs( v, longNormalForm( e_ ) )
      case Apps( e, es ) =>
        e.ty match {
          case FunctionType( _, ts ) =>
            val names = new NameGenerator( freeVariables( e ).map { _.name } )
            val etaVars = ts.drop( es.length ).map { t => names.fresh( Var( "η", t ) ) }
            Abs.Block(
              etaVars,
              Apps(
                e,
                es.map { longNormalForm( _ ) } ++ etaVars.map { longNormalForm( _ ) } ) )
        }
    }
}
