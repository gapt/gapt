/*
 * Substitutions.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language

import at.logic.language.Symbols._
import at.logic.language.TypedLambdaCalculus._
import scala.collection.immutable._

object Substitutions {

    case class SingleSubstitution(variable: Var, expression: LambdaExpression) {
        def _1 = variable
        def _2 = expression

        def apply(expression: LambdaExpression):LambdaExpression = substituteWithRenaming(expression)

        private def substituteWithRenaming(exp: LambdaExpression):LambdaExpression = {
            val eFV = expression.getFreeAndBoundVariables._1
            exp match {
                case x:Var => if (x == variable)  expression else x
                case App(m,n) => App(substituteWithRenaming(m), substituteWithRenaming(n))
                case Abs(x,m) => if (x == variable) exp
                                 else {                                     
                                     if (eFV.contains(x)) {
                                         val Abs(y,n) = renameBoundVariable(Abs(x,m), eFV)
                                         Abs(y,substituteWithRenaming(n))
                                     }
                                     else Abs(x,substituteWithRenaming(m))
                                 }
            }
        }

        private def renameBoundVariable(exp: Abs, disallowedVariables: Set[Var]) = exp match {
           case Abs(x,m) => {
                   val (eFV,eBV) = exp.getFreeAndBoundVariables
                   val disallowed = disallowedVariables ++ eFV
                   val v = freshVar(x.exptype, disallowed)
                   val sigma: SingleSubstitution = (x,v)
                   val n = sigma(m)
                   Abs(v,n)
           }
        }
        private def substitute(exp: LambdaExpression):LambdaExpression = exp match {
                case x:Var => if (x == variable)  expression else x
                case App(m,n) => App(substitute(m), substitute(n))
                case Abs(x,m) => if (x == variable) expression
                                 else Abs(x,substitute(m))
        }
    }
    implicit def convertPairToSingleSubstitution(pair: Tuple2[Var,LambdaExpression]):SingleSubstitution = SingleSubstitution(pair._1, pair._2)
    implicit def convertSingleSubstitutionToPair(sub: SingleSubstitution):Tuple2[Var,LambdaExpression] = (sub.variable, sub.expression)



    case class Substitution(substitutions: List[SingleSubstitution]) extends (LambdaExpression => LambdaExpression) {
        def this(subs: SingleSubstitution*) = this(subs.toList)
        def this(variable: Var, expression: LambdaExpression) = this(List(SingleSubstitution(variable, expression)))

        def ::(sub:SingleSubstitution) = new Substitution(sub::substitutions)
        def :::(otherSubstitutionList:Substitution) = new Substitution(otherSubstitutionList.substitutions:::this.substitutions)
        def apply(expression: LambdaExpression):LambdaExpression = {
            var result = expression       // ToDo: Replace this by an immutable and more functional alternative...
            for ( sigma <- substitutions ) result = sigma(result)
            result
        }
    }
    implicit def convertPairToSubstitution(pair: Tuple2[Var,LambdaExpression]):Substitution = new Substitution(pair._1, pair._2)
    implicit def convertSubstitutionToPair(sub: Substitution):Tuple2[Var,LambdaExpression] = {
        require(sub.substitutions.length == 1)
        (sub.substitutions.head.variable, sub.substitutions.head.expression)
    }
    implicit def convertSingleSubstitutionToSubstitution(sub: SingleSubstitution):Substitution = new Substitution(sub.variable, sub.expression)
    implicit def convertSubstitutionToSingleSubstitution(sub: Substitution):SingleSubstitution = {
        require(sub.substitutions.length == 1)
        sub.substitutions.head
    }

//    def betaReduce(redex: LambdaExpression) = {
//        redex match {
//            case App(Abs(x,body),arg) => substitute(body, (x,arg))
//            case _ => throw new IllegalArgumentException
//        }
//    }



}
