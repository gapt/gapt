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

object LogicExpressions {

    val negS = LatexSymbol("\\neg", "neg")          ; val negC = Var(negS, "(o -> o)")
    val andS = LatexSymbol("\\wedge", "and")        ; val andC = Var(andS, "(o -> (o -> o))")
    val orS = LatexSymbol("\\vee", "or")            ; val orC  = Var(orS, "(o -> (o -> o))")
    val impS = LatexSymbol("\\rightarrow", "imp")   ; val impC  = Var(impS, "(o -> (o -> o))")

    val exS = LatexSymbol("\\exists", "ex")         ; def exQ(exptype:TA) = Var(exS, ->(exptype,"o"))
    val allS = LatexSymbol("\\forall", "all")       ; def allQ(exptype:TA) = Var(allS, ->(exptype,"o"))

    trait LogicExpression extends LambdaExpression {
        def and(that: LogicExpression) = new And(this, that)
        def or(that: LogicExpression) = new Or(this, that)
        def imp(that: LogicExpression) = new Imp(this, that)
    }

    case class Atom(predicate: LambdaExpression, arguments:List[LambdaExpression])
        //Todo extends App(...)

    case class Neg(sub: LogicExpression) extends App(negC,sub) with LogicExpression
    case class And(left: LogicExpression, right: LogicExpression) extends App(App(andC,left),right) with LogicExpression
    case class Or(left: LogicExpression, right: LogicExpression) extends App(App(orC,left),right) with LogicExpression
    case class Imp(left: LogicExpression, right: LogicExpression) extends App(App(impC,left),right) with LogicExpression

    //case class Ex(sub: LogicExpression) extends App(exQ(sub.exptype),sub) with LogicExpression
    //case class All(sub: LogicExpression) extends App(allQ(sub.exptype),sub) with LogicExpression
    //case class ExVar(variable: Var, sub: LogicExpression) extends Ex(Abs(variable, sub))
    //case class AllVar(variable: Var, sub: LogicExpression) extends All(Abs(variable, sub))
    case class Ex(sub: LambdaExpression) extends App(exQ(sub.exptype),sub) with LogicExpression
    case class All(sub: LambdaExpression) extends App(allQ(sub.exptype),sub) with LogicExpression
    case class ExVar(variable: Var, subformula: LambdaExpression) extends Ex(Abs(variable, subformula))
    case class AllVar(variable: Var, subformula: LambdaExpression) extends All(Abs(variable, subformula))
}
