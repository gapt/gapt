/*
 * LogicExpressions.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language

import Symbols._
import TypedLambdaCalculus._
import Types._
import Types.TAImplicitConverters._

object LogicExpressions {  // change to "BooleanConnectives"

    val negS = LatexSymbol("\\neg", "neg")          ; val negC = Var(negS, "(o -> o)")
    val andS = LatexSymbol("\\wedge", "and")        ; val andC = Var(andS, "(o -> (o -> o))")
    val orS = LatexSymbol("\\vee", "or")            ; val orC  = Var(orS, "(o -> (o -> o))")
    val impS = LatexSymbol("\\rightarrow", "imp")   ; val impC  = Var(impS, "(o -> (o -> o))")

    trait LogicExpression extends LambdaExpression {   // change to "BooleanExpression"
        def and(that: LambdaExpression) = And(this, that)
        def or(that: LambdaExpression) = Or(this, that)
        def imp(that: LambdaExpression) = Imp(this, that)
    }

    object Atom {
        def apply(predicate: LambdaExpression, arguments:List[LambdaExpression]) = new App(AppN(predicate,arguments.take(arguments.length - 1)),arguments.last) with LogicExpression
        def unapply(expression: LambdaExpression):Option[(LambdaExpression, List[LambdaExpression])] = expression.exptype match {
            case To() => Some(unapplyRec(expression))
            case _ => None
        }

        private def unapplyRec(expression: LambdaExpression): (LambdaExpression, List[LambdaExpression]) = expression match {
            case App(f,arg) => (unapplyRec(f)._1, unapplyRec(f)._2 ::: (arg::Nil) )
            case v: Var => (v,Nil)
            case a: Abs => (a,Nil)
        }
    }

    object Neg {
        def apply(sub: LambdaExpression) = new App(negC,sub) with LogicExpression
        def unapply(expression: LambdaExpression) = expression match {
            case App(negC,sub) => Some( (sub) )
            case _ => None
        }
    }

    object And {
        def apply(left: LambdaExpression, right: LambdaExpression) = new App(App(andC,left),right) with LogicExpression
        def unapply(expression: LambdaExpression) = expression match {
            case App(App(andC,left),right) => Some( (left,right) )
            case _ => None
        }
    }

    object Or {
        def apply(left: LambdaExpression, right: LambdaExpression) = new App(App(orC,left),right) with LogicExpression
        def unapply(expression: LambdaExpression) = expression match {
            case App(App(orC,left),right) => Some( (left,right) )
            case _ => None
        }
    }

    object Imp {
        def apply(left: LambdaExpression, right: LambdaExpression) = new App(App(impC,left),right) with LogicExpression
        def unapply(expression: LambdaExpression) = expression match {
            case App(App(impC,left),right) => Some( (left,right) )
            case _ => None
        }
    }

}
