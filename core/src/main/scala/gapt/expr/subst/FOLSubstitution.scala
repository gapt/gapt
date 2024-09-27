package gapt.expr.subst

import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLVar

import scala.collection.Iterable

class FOLSubstitution(val folmap: Map[FOLVar, FOLTerm]) extends Substitution(folmap.asInstanceOf[Map[Var, Expr]]) {

  /**
   * Applies this substitution to an object.
   *
   * @param x The object to be substituted.
   * @param ev Testifies that applying a FOLSubstitution to an element of type T will result in an element of type U.
   * @tparam T The type of x.
   * @tparam U The type of x substituted.
   * @return
   */
  def apply[T, U](x: T)(implicit ev: Substitutable[FOLSubstitution, T, U], dummyImplicit: DummyImplicit): U = ev.applySubstitution(this, x)

  def compose(sub: FOLSubstitution): FOLSubstitution = {
    val newMap = for ((x1, x2) <- sub.folmap) yield {
      val x2_ = apply(x2)
      (x1, x2_)
    }
    FOLSubstitution(folmap ++ newMap)
  }
}
object FOLSubstitution {
  def apply(subs: Iterable[(FOLVar, FOLTerm)]): FOLSubstitution = new FOLSubstitution(Map() ++ subs)
  def apply(subs: (FOLVar, FOLTerm)*): FOLSubstitution = new FOLSubstitution(Map() ++ subs)
  def apply(variable: FOLVar, term: FOLTerm): FOLSubstitution = new FOLSubstitution(Map(variable -> term))
  def apply(map: Map[FOLVar, FOLTerm]): FOLSubstitution = new FOLSubstitution(map)
  def apply() = new FOLSubstitution(Map())
}
