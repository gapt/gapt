/*
 * Substitutions.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.lambda

import Symbols._
import TypedLambdaCalculus._
import scala.collection.immutable._



object Substitutions {
    case class SingleSubstitution[A <: Lambda](variable: Var[A], expression: LambdaExpression[A]) {
        def _1 = variable
        def _2 = expression

        def apply(expression: LambdaExpression[A])(implicit factory1: AbsFactory[A], factory2: AppFactory[A]):LambdaExpression[A] = substituteWithRenaming(expression)

        private def substituteWithRenaming(exp: LambdaExpression[A])(implicit factory1: AbsFactory[A], factory2: AppFactory[A]):LambdaExpression[A] = {
            val eFV = expression.getFreeAndBoundVariables._1
            exp match {
                case x:Var[_] => if (x == variable)  expression else x
                case App(m,n) => App(substituteWithRenaming(m.asInstanceOf[LambdaExpression[A]]), substituteWithRenaming(n.asInstanceOf[LambdaExpression[A]]))
                case Abs(x,m) => if (x == variable) exp
                                 else {                                     
                                     if (eFV.contains(x)) {
                                         val Abs(y,n) = renameBoundVariable(Abs(x,m.asInstanceOf[LambdaExpression[A]]), eFV)
                                         Abs(y.asInstanceOf[Var[A]],substituteWithRenaming(n.asInstanceOf[LambdaExpression[A]]))
                                     }
                                     else Abs(x.asInstanceOf[Var[A]],substituteWithRenaming(m.asInstanceOf[LambdaExpression[A]]))
                                 }
            }
        }

        private def renameBoundVariable[A <: Lambda](exp: Abs[A], disallowedVariables: List[Var[A]])(implicit factory1: AbsFactory[A], factory2: AppFactory[A], factory3: VarFactory[A]) = exp match {
           case Abs(x,m) => {
                   val (eFV,eBV) = exp.getFreeAndBoundVariables
                   val disallowed = disallowedVariables ++ eFV
                   val v = freshVar[A](x.exptype, disallowed)
                   val sigma: SingleSubstitution[A] = SingleSubstitution(x.asInstanceOf[Var[A]],v)
                   val n = sigma(m.asInstanceOf[LambdaExpression[A]])
                   Abs(v,n)
           }
        }
        private def substitute(exp: LambdaExpression[A])(implicit factory1: AbsFactory[A], factory2: AppFactory[A]):LambdaExpression[A] = exp match {
                case x:Var[_] => if (x == variable)  expression else x
                case App(m,n) => App(substitute(m.asInstanceOf[LambdaExpression[A]]), substitute(n.asInstanceOf[LambdaExpression[A]]))
                case Abs(x,m) => if (x == variable) expression
                                 else Abs(x.asInstanceOf[Var[A]],substitute(m.asInstanceOf[LambdaExpression[A]]))
        }
    }
    implicit def convertPairToSingleSubstitution[A <: Lambda](pair: Tuple2[Var[A],LambdaExpression[A]]):SingleSubstitution[A] = SingleSubstitution(pair._1, pair._2)
    implicit def convertSingleSubstitutionToPair[A <: Lambda](sub: SingleSubstitution[A]):Tuple2[Var[A],LambdaExpression[A]] = (sub.variable, sub.expression)



    case class Substitution[A <: Lambda](substitutions: List[SingleSubstitution[A]])(implicit factory1: AbsFactory[A], factory2: AppFactory[A]) extends (LambdaExpression[A] => LambdaExpression[A]) {

        def this(subs: SingleSubstitution[A]*)(implicit factory1: AbsFactory[A], factory2: AppFactory[A]) = this(subs.toList)
        def this(variable: Var[A], expression: LambdaExpression[A])(implicit factory1: AbsFactory[A], factory2: AppFactory[A]) = this(List(SingleSubstitution(variable, expression)))

        def ::(sub:SingleSubstitution[A]) = new Substitution(sub::substitutions)
        def :::(otherSubstitutionList:Substitution[A]) = new Substitution(otherSubstitutionList.substitutions:::this.substitutions)
        def apply(expression: LambdaExpression[A]):LambdaExpression[A] = {
            var result = expression       // ToDo: Replace this by an immutable and more functional alternative...
            for ( sigma <- substitutions ) result = sigma(result)
            result
        }
    }
    implicit def convertPairToSubstitution[A <: Lambda](pair: Tuple2[Var[A],LambdaExpression[A]])(implicit factory1: AbsFactory[A], factory2: AppFactory[A]):Substitution[A] = new Substitution[A](pair._1, pair._2)
    implicit def convertSubstitutionToPair[A <: Lambda](sub: Substitution[A]):Tuple2[Var[A],LambdaExpression[A]] = {
        require(sub.substitutions.length == 1)
        (sub.substitutions.head.variable, sub.substitutions.head.expression)
    }
    implicit def convertSingleSubstitutionToSubstitution[A <: Lambda](sub: SingleSubstitution[A])(implicit factory1: AbsFactory[A], factory2: AppFactory[A]):Substitution[A] = new Substitution[A](sub.variable, sub.expression)
    implicit def convertSubstitutionToSingleSubstitution[A <: Lambda](sub: Substitution[A]):SingleSubstitution[A] = {
        require(sub.substitutions.length == 1)
        sub.substitutions.head
    }
}
