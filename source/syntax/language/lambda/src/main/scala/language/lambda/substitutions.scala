package at.logic.language.lambda

import symbols._
import typedLambdaCalculus._

package substitutions {

  /* substitution preserves the following:
   * 1) it is a valid function, i.e. order of elements is irrelevant and each varialbe is mapped to only one element
   * 2) all mappings are applied simultaneously to a term i.e. {x |-> y, y |-> a}x = y and not a.
   */
  class Substitution protected[substitutions](val map: scala.collection.immutable.Map[Var, LambdaExpression]) extends (LambdaExpression => LambdaExpression) {
    def ::(sub:Tuple2[Var, LambdaExpression]) = new Substitution(map + sub)
    def :::(otherSubstitution:Substitution) = new Substitution(map ++ otherSubstitution.map.elements)
    def apply(expression: LambdaExpression): LambdaExpression = applyWithChangeDBIndices(expression)
    override def equals(a: Any) = a match {
      case s: Substitution => map.equals(s.map)
      case _ => false
    }
    override def hashCode() = map.hashCode
    override def toString = map.toString
    // the change of db indices is done automatically in the constructor of abs
    private def applyWithChangeDBIndices(expression: LambdaExpression): LambdaExpression = expression match {
      case x:Var if x.isFree => map.get(x) match {
          case Some(t) => t
          case None => x
      }
      case App(m,n) => App(applyWithChangeDBIndices(m), applyWithChangeDBIndices(n))
      case abs: Abs => Abs(abs.variable ,applyWithChangeDBIndices(abs.expressionInScope))
      case _ => expression
    }
    // make sure the overriden keys are of the applying sub
    def compose(sub: Substitution): Substitution = Substitution(map ++ sub.map.map(x => (x._1, apply(x._2))))
  }

  object Substitution {
    def apply(subs: Iterator[Tuple2[Var, LambdaExpression]]): Substitution = new Substitution(new scala.collection.immutable.HashMap[Var, LambdaExpression]() ++ subs)
    def apply(subs: Tuple2[Var, LambdaExpression]*): Substitution = apply(subs.elements)
    def apply(subs: List[Tuple2[Var, LambdaExpression]]): Substitution = apply(subs.elements)
    def apply(variable: Var, expression: LambdaExpression): Substitution = apply((variable, expression))
    def apply(map: scala.collection.immutable.Map[Var, LambdaExpression]): Substitution = new Substitution( map )
    def apply() = new Substitution(new scala.collection.immutable.EmptyMap)
  }
  
  object ImplicitConverters {
    implicit def convertSubstitutionToPair(sub: Substitution): Tuple2[Var,LambdaExpression] = {
      require(sub.map.size == 1)
      sub.map.elements.next
    }
    implicit def convertPairToSubstitution(pair: Tuple2[Var, LambdaExpression]): Substitution = Substitution(pair)
  }
}
