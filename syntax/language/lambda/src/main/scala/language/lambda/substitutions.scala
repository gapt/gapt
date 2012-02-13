package at.logic.language.lambda

import symbols._
import typedLambdaCalculus._

package substitutions {

import collection.immutable.HashSet

/* substitution preserves the following:
* 1) it is a valid function, i.e. order of elements is irrelevant and each varialbe is mapped to only one element
* 2) all mappings are applied simultaneously to a term i.e. {x |-> y, y |-> a}x = y and not a.
*/
  class Substitution[T <: LambdaExpression] protected[substitutions](val map: scala.collection.immutable.Map[Var, T]) extends (T => T) {
    def ::(sub:Tuple2[Var, T]) = new Substitution(map + sub)
    def :::(otherSubstitution:Substitution[T]) = new Substitution(map ++ otherSubstitution.map.iterator)
    def apply(expression: T): T = applyWithChangeDBIndices(expression)
    override def equals(a: Any) = a match {
      case s: Substitution[_] => map.equals(s.map)
      case _ => false
    }
    override def hashCode() = map.hashCode
    override def toString = map.toString

    /*copy of a method in Sequent */
    def checkLambdaExpression(t: LambdaExpression) = checkLambdaExpression_(t, HashSet[Var]())
    def checkLambdaExpression_(t: LambdaExpression, scope: HashSet[Var]) : List[Var] = t match {
      case v : Var  =>
        if (scope.contains(v) && v.isFree) return List(v)
        if ((!scope.contains(v)) && v.isBound) return List(v)
        List()
      case App(s,t) =>
        checkLambdaExpression_(s,scope) ++ checkLambdaExpression_(t,scope)
      case AbsInScope(v,t) =>
        checkLambdaExpression_(t, scope + v)
      case _ => throw new Exception("Unhandled Lambda Term Type (not var, abs nor app)")
    }

    // the change of db indices is done automatically in the constructor of abs
    protected def applyWithChangeDBIndices(expression: T): T = expression match {
      case x:Var if x.isFree => {
        map.get(x) match {
          case Some(t) => {
            val freevarsWithDBIndex = checkLambdaExpression(t)
            if (!freevarsWithDBIndex.isEmpty) {
              println("ERROR: bound variables "+ freevarsWithDBIndex +" outside of binding context in term "+t.toStringSimple)
              throw new Exception("ERROR: bound variables "+ freevarsWithDBIndex +" outside of binding context in term "+t.toStringSimple)
            }

            //println("substituting " + t.toStringSimple + " for " + x.toStringSimple)
            t
          }
          case None => {
            //println(x + " is free, but we don't substitute for it")
            x.asInstanceOf[T]
          }
      }
    }
      case x:Var if !x.isFree => {
        if (map.contains( x ) )
          println("WARNING: trying to substitute for a bound variable, ignoring!") 
       expression 
      }
      case App(m,n) => App(applyWithChangeDBIndices(m.asInstanceOf[T]), applyWithChangeDBIndices(n.asInstanceOf[T])).asInstanceOf[T]
      case abs: Abs => Abs(abs.variable ,applyWithChangeDBIndices(abs.expressionInScope.asInstanceOf[T])).asInstanceOf[T]
      case _ => expression
    }

    // make sure the overriden keys are of the applying sub
    // note: compose is in function application notation i.e. (sigma compose tau) apply x = sigma(tau(x)) = x.tau.sigma
    def compose(sub: Substitution[T]): Substitution[T] = Substitution(map ++ sub.map.map(x => (x._1, apply(x._2))))

    def isRenaming = map.forall( p => p._2.isInstanceOf[Var] )
  }

  object Substitution {
    def apply[T <: LambdaExpression](subs: Iterator[Tuple2[Var, T]]): Substitution[T] = new Substitution(new scala.collection.immutable.HashMap[Var, T]() ++ subs)
    def apply[T <: LambdaExpression](subs: Tuple2[Var, T]*): Substitution[T] = apply(subs.iterator)
    def apply[T <: LambdaExpression](subs: List[Tuple2[Var, T]]): Substitution[T] = apply(subs.iterator)
    def apply[T <: LambdaExpression](variable: Var, expression: T): Substitution[T] = apply((variable, expression))
    def apply[T <: LambdaExpression](map: scala.collection.immutable.Map[Var, T]): Substitution[T] = new Substitution( map )
    def apply() = new Substitution(new scala.collection.immutable.HashMap())
  }
  
  object ImplicitConverters {
    implicit def convertSubstitutionToPair[T <: LambdaExpression](sub: Substitution[T]): Tuple2[Var,T] = {
      require(sub.map.size == 1)
      sub.map.iterator.next
    }
    implicit def convertPairToSubstitution[T <: LambdaExpression](pair: Tuple2[Var, T]): Substitution[T] = Substitution(pair)
  }
}
