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

        def apply(expression: LambdaExpression):LambdaExpression = substituteWithRenaming(expression, this)

        private def substituteWithRenaming(expression: LambdaExpression, sigma: SingleSubstitution):LambdaExpression = expression match {
                case x:Var => if (x == sigma.variable)  sigma.expression else x
                case App(m,n) => App(substituteWithRenaming(m,sigma), substituteWithRenaming(n,sigma))
                case Abs(x,m) => if (x == sigma.variable) expression
                                 else {
                                     val eFV = sigma.expression.getFreeAndBoundVariables._1
                                     if (eFV.contains(x)) {
                                         val Abs(y,n) = renameBoundVariable(Abs(x,m))
                                         Abs(y,substituteWithRenaming(n, sigma))
                                     }
                                     else Abs(x,substituteWithRenaming(m, sigma))
                                 }
        }

        private def renameBoundVariable(exp: Abs) = exp match {
           case Abs(x,m) => {
                    val v = freshVar(x.exptype)
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

        def ::(sub:SingleSubstitution) = new Substitution(sub::substitutions)
        def :::(otherSubstitutionList:Substitution) = new Substitution(otherSubstitutionList.substitutions:::this.substitutions)
        def apply(expression: LambdaExpression):LambdaExpression = {
            var result = expression       // ToDo: Replace this by an immutable and more functional alternative...
            for ( s <- substitutions ) result = substituteWithRenaming(result, s)
            result
        }

        private def substitute(expression: LambdaExpression, sigma: SingleSubstitution):LambdaExpression = expression match {
                case x:Var => if (x == sigma.variable)  sigma.expression else x
                case App(m,n) => App(substitute(m,sigma), substitute(n,sigma))
                case Abs(x,m) => if (x == sigma.variable) expression
                                 else Abs(x,substitute(m, sigma))
        }


        private def substituteWithRenaming(expression: LambdaExpression, sigma: SingleSubstitution):LambdaExpression = expression match {
                case x:Var => if (x == sigma.variable)  sigma.expression else x
                case App(m,n) => App(substitute(m,sigma), substitute(n,sigma))
                case Abs(x,m) => if (x == sigma.variable) expression
                                 else {
                                     val eFV = sigma.expression.getFreeAndBoundVariables._1
                                     if (eFV.contains(x)) {
                                         val Abs(y,n) = renameBoundVariable(Abs(x,m))
                                         Abs(y,substituteWithRenaming(n, sigma))
                                     }
                                     else Abs(x,substituteWithRenaming(m, sigma))
                                 }

        }

        private def renameBoundVariable(expression: Abs) = expression match {
           case Abs(x,m) => {
                    val v = freshVar(x.exptype)
                    val n = substitute(m,(x,v))
                    Abs(v,n)
            }
        }
    }

//
//
//    private def substituteRec(expression: LambdaExpression, substitution: Substitution, boundVariables:Set[Var]): LambdaExpression = {
//        val (v, t) = substitution
//        expression match {
//            case x:Var => if ( (x == v) && !(boundVariables.contains(x)) ) t else x
//            case App(m,n) => App(substitute(m,(v,t)), substitute(n,(v,t)))
//            case Abs(x,m) => if (x == v) substitute(renameBoundVariables(expression, Set(x)), (v,t))  // this line can be optimized
//                             else Abs(x,substitute(m, (v,t)))
//        }
//    }

//    def betaReduce(redex: LambdaExpression) = {
//        redex match {
//            case App(Abs(x,body),arg) => substitute(body, (x,arg))
//            case _ => throw new IllegalArgumentException
//        }
//    }

//    def renameBoundVariables(expression:LambdaExpression, environment: Set[Var]):LambdaExpression = expression match {
//        case Abs(x,m) => if (environment.contains(x)) {
//                            val v = freshVar(x.exptype)
//                            val n = substitute(m,(x,v))
//                            val newEnvironment = environment + v
//                            Abs(v, renameBoundVariables(n, newEnvironment) )
//                         }
//                         else Abs(x,renameBoundVariables(m, environment))
//        case App(m, n) => App(renameBoundVariables(m, environment), renameBoundVariables(n, environment))
//        case expression:Var => expression
//    }



}
