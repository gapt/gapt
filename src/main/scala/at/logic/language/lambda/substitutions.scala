
package at.logic.language.lambda

import symbols._

/* 
 * A substitution is a mapping from variables to lambda-expressions which differs from the identity
 * on finitely many variables. Therefore:
 *  1) each variable is mapped to only one lambda expression
 *  2) the order of the variable-mappings is irrelevant
 *  3) all variable-mappings are applied simultaneously to a term i.e. {x |-> y, y |-> a}x = y and not a.
 *
 * As the lambda calculus contains variable binders, substitution can only be defined up to alpha-equivalence.
 * When applying a substitution, bound variables are renamed if needed.
 */
class Substitution(val map: Map[Var, LambdaExpression]) {
 
  // Require that each variable is substituted by a term of the same type
  for( s <- map) require( s._1.exptype == s._2.exptype,
                          "Error creating substitution: variable "+s._1+" has type "+s._1.exptype+
                          " but subterm "+s._2+" has type "+s._2.exptype )

  // Substitution (capture-avoiding)
  // as in http://en.wikipedia.org/wiki/Lambda_calculus#Capture-avoiding_substitutions   
  def apply(t: LambdaExpression): LambdaExpression = t match {
    case v : Var if map.contains(v) => map(v)
    case v : Var if !map.contains(v) => v
    case Const(_, _) => t
    case App(t1, t2) =>
      App( apply(t1), apply(t2) )
    case Abs(v, t1) =>
      val fv = range
      val dom = domain
      
      val newSub = if (domain.contains(v)) {
        // Abs(x, t) [x -> u] = Abs(x, t)
        // The replacement of v is not done, removing it from the substitution and applying to t1
        val newMap = map - v
        Substitution(newMap)
      } else this
      
      val (freshVar, newTerm) = if (fv.contains(v)) {
        // Variable captured, renaming the abstracted variable
        val freshVar = rename(v, fv)
        val sub = Substitution(v, freshVar)
        val newTerm = sub(t1)
	(freshVar, newTerm)
      } else (v, t1)

      Abs(freshVar, newSub(newTerm))
  }

  def domain : List[Var] = map.keys.toList
  def range : List[Var] = map.foldLeft(List[Var]()) ( (acc, data) => freeVariables(data._2) ++ acc )

  def ::(sub: (Var, LambdaExpression)) = new Substitution(map + sub)
  def ::(otherSubstitution: Substitution) = new Substitution(map ++ otherSubstitution.map)

  override def equals(a: Any) = a match {
    case s: Substitution => map.equals(s.map)
    case _ => false
  }

  // an identity function maps all variables to themselves
  def isIdentity = map.filterNot((p : (Var, LambdaExpression)) => p._1 == p._2).isEmpty

  // make sure the overriden keys are of the applying sub
  // note: compose is in function application notation i.e. (sigma compose tau) apply x = sigma(tau(x)) = x.tau.sigma
  def compose(sub: Substitution): Substitution = Substitution(map ++ sub.map.map(x => (x._1, apply(x._2))))

  //REMARK: this does not imply the substitution is injective
  def isRenaming = map.forall( p => p._2.isInstanceOf[Var] )

  //TODO: implement
  def isInjectiveRenaming = throw new Exception("Not yet implemented!")

  override def toString() = map.map(x => x._1 +" -> "+x._2).mkString("Substitution(",",",")")

}

object Substitution {
  def apply(subs: List[(Var, LambdaExpression)]): Substitution = new Substitution(Map() ++ subs)
  def apply(variable: Var, expression: LambdaExpression): Substitution = new Substitution(Map(variable -> expression))
  def apply(map: Map[Var, LambdaExpression]): Substitution = new Substitution( map )
  def apply() = new Substitution(Map())
}

