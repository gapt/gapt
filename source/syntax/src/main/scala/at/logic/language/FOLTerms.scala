/*
 * FOLTerms.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language


import Symbols._
import TypedLambdaCalculus._
import Types._
import Types.TAImplicitConverters._
import LogicExpressions._

object FOLTerms {
    trait FOLTerm extends LambdaExpression

    object Constant {
        def apply(s: String) = new Var(StringSymbol(s), i) with FOLTerm
        def unapply(expression: LambdaExpression) = expression match {
            case Var(StringSymbol(s), Ti()) => Some( (s) )
            case _ => None
        }
    }

    object Function {
        def apply(fName:String, arguments:List[FOLTerm]) = {
            val fType = ((arguments.map((x:Any) => i):List[TA]) :\ (i:TA))(->)  // computing the type of the function Var.
            val f = Var(StringSymbol(fName),fType)                              // creating the function Var.
            new App(AppN(f,arguments.take(arguments.length - 1)),arguments.last) with FOLTerm
        }
        def unapply(expression: LambdaExpression): Option[(String, List[FOLTerm])] = None  // ToDo

// ToDo        private def unapplyRec(expression: LambdaExpression): (LambdaExpression, List[LambdaExpression]) = expression match {
//            case App(f,arg) => (unapplyRec(f)._1, unapplyRec(f)._2 ::: (arg::Nil) )
//            case v: Var => (v,Nil)
//            case a: Abs => (a,Nil)
//        }
    }


// ToDelete   object Atom {
//        def apply(predicate: LambdaExpression, arguments:List[LambdaExpression]) = new App(AppN(predicate,arguments.take(arguments.length - 1)),arguments.last) with LogicExpression
//        def unapply(expression: LambdaExpression):Option[(LambdaExpression, List[LambdaExpression])] = expression.exptype match {
//            case To() => Some(unapplyRec(expression))
//            case _ => None
//        }
//
//
//    }
}
