package gapt.expr.subst

import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLVar
import gapt.expr.util.freeVariables
import gapt.expr.subst.Substitutable.SubstitutableTy
import gapt.expr.ty.TVar
import gapt.expr.ty.Ty

/**
 * An unvalidated substitution, you should use [[Substitution]] instead.
 */
class PreSubstitution(val map: Map[Var, Expr], val typeMap: Map[TVar, Ty]) {

  def domain: Set[Var] = map.keySet
  def range: Set[Var] = map.values.toSet[Expr].flatMap(freeVariables(_))

  override def hashCode: Int = map.hashCode ^ typeMap.hashCode

  override def equals(a: Any): Boolean = a match {
    case s: PreSubstitution => map == s.map && typeMap == s.typeMap
    case _                  => false
  }

  def isIdentity: Boolean = map.forall(p => p._1 == p._2) && typeMap.forall(p => p._1 == p._2)

  def isRenaming: Boolean = map.forall(p => p._2.isInstanceOf[Var])

  def isInjectiveRenaming: Boolean = domain.forall { v => map(v).isInstanceOf[Var] && domain.forall { u => u == v || map(u) != map(v) } }

  def isEmpty: Boolean = map.isEmpty && typeMap.isEmpty

  private[expr] def applyToTypeOnly(v: Var): Var =
    if (typeMap.isEmpty) v else Var(v.name, SubstitutableTy.applySubstitution(this, v.ty))

  // Special-cased for performance
  def apply(v: Var): Expr =
    map.getOrElse(v, applyToTypeOnly(v))

  override def toString: String =
    s"Substitution(${
        (map.toSeq.sortBy(_._1.name) ++ typeMap.toSeq.sortBy(_._1.name)).map(x => s"${x._1} -> ${x._2}").mkString(", ")
      })"

  def asFOLSubstitution: FOLSubstitution = {
    require(typeMap.isEmpty)
    FOLSubstitution(map map {
      case (l: FOLVar, r: FOLTerm) => l -> r
      case (l, r)                  => throw new MatchError(l -> r)
    })
  }

  def +(v: Var, t: Expr): PreSubstitution = new PreSubstitution(map + ((v, t)), typeMap)
  def +(v: TVar, t: Ty): PreSubstitution = new PreSubstitution(map, typeMap + ((v, t)))

  def toSubstitution: Substitution = Substitution(map, typeMap)

}

object PreSubstitution {
  val empty = new PreSubstitution(Map(), Map())
  def apply(): PreSubstitution = empty
  def apply(map: Iterable[(Var, Expr)]): PreSubstitution = new PreSubstitution(map.toMap, Map())
}
