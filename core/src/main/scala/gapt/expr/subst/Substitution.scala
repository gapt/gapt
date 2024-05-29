package gapt.expr.subst

import gapt.expr.App
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.subst.Substitutable.SubstitutableTy
import gapt.expr.ty.TVar
import gapt.expr.ty.Ty

/**
 * A substitution is a mapping from variables to lambda-expressions which differs from the identity
 * on finitely many variables. Therefore:
 *  1) each variable is mapped to only one lambda expression
 *  2) the order of the variable-mappings is irrelevant
 *  3) all variable-mappings are applied simultaneously to a term i.e. {x |-> y, y |-> a}x = y and not a.
 *
 * As the lambda calculus contains variable binders, substitution can only be defined up to alpha-equivalence.
 * When applying a substitution, bound variables are renamed if needed.
 */
class Substitution(map: Map[Var, Expr], typeMap: Map[TVar, Ty] = Map()) extends PreSubstitution(map, typeMap) {

  for ((v, t) <- map)
    require(
      SubstitutableTy.applySubstitution(this, v.ty) == t.ty,
      s"Error creating substitution: variable $v has type ${v.ty} but subterm $t has type ${t.ty}"
    )

  /**
   * Applies this substitution to an object.
   *
   * @param x The object to be substituted.
   * @param ev Testifies that applying a Substitution to an element of type T will result in an element of type U.
   * @tparam T The type of x.
   * @tparam U The type of x substituted.
   * @return
   */
  def apply[T, U](x: T)(implicit ev: Substitutable[Substitution, T, U]): U = ev.applySubstitution(this, x)

  // Special-cased for performance
  override def apply(v: Var): Expr = super.apply(v)

  /** Compose two substitutions such that `(a compose b)(x) == a(b(x))`. */
  def compose(that: Substitution): Substitution =
    Substitution(
      (domain ++ that.domain).map(v => v -> this(that(v))),
      (this.typeMap.keySet ++ that.typeMap.keySet).map(v => (v, this(that(v))))
    )

  def restrict(newDomain: Iterable[Var]): Substitution =
    Substitution(newDomain.view.map(v => v -> this(v)), typeMap)

  def isInjectiveOnDomain: Boolean = isInjective(domain)
  def isInjective(dom: Set[Var]): Boolean =
    dom.forall { x =>
      val images = (dom - x).map(apply(_))
      def solve(term: Expr): Boolean =
        images(term) || (term match {
          case Const(_, _, _) => true
          case App(a, b)      => solve(a) && solve(b)
          case Var(_, _)      => false
        })
      !solve(map(x))
    }

}

object Substitution {
  def apply(subs: Iterable[(Var, Expr)], tySubs: Iterable[(TVar, Ty)] = Nil): Substitution =
    new Substitution(Map() ++ subs, Map() ++ tySubs)
  def apply(subs: (Var, Expr)*): Substitution = new Substitution(Map() ++ subs)
  def apply(variable: Var, expression: Expr): Substitution = new Substitution(Map(variable -> expression))
  def apply(map: Map[Var, Expr]): Substitution = new Substitution(map)
  def apply() = new Substitution(Map())
}
