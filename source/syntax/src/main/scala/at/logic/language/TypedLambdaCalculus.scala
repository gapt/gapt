/*
 * typedLambdaCalculus.scala
 *
 */

package at.logic.language

import at.logic.language.Symbols._

object TypedLambdaCalculus {

    import at.logic.language.Types._
    
    
    abstract class LambdaExpression {
        def exptype: TA
    }


    case class Var(name: SymbolA, exptype: TA )
        extends LambdaExpression

    case class Abs(variable: Var, expression: LambdaExpression)
        extends LambdaExpression {
            def exptype: TA = ->(variable.exptype,expression.exptype)
        }

    case class App(function: LambdaExpression, argument: LambdaExpression )
        extends LambdaExpression {
            require({
                function.exptype match {
                    case ->(in,out) => {if (in == argument.exptype) true
                                        else false}
                    case _          => false
                }
            })
            def exptype: TA = {
                function.exptype match {
                    case ->(in,out) => out
                }
            }
        }


//    case class AbsN(variables: ::[Var], override val expression: LambdaExpression)
//        extends Abs(variables.head,
//                    variables.tail match {
//                        case Nil => expression
//                        case h::t => AbsN(::(h,t),expression)
//                    }
//                   )

//    case class AbsN(variables: List[Var], override val expression: LambdaExpression)
//        extends Abs(variables.head,
//                    if (variables.tail.isEmpty) expression
//                    else AbsN(variables.tail,expression)
//                   ) {
//            require(!variables.isEmpty)
//        }

//    case class AbsN(variables: List[Var], expression: LambdaExpression)
//        extends LambdaExpression {
//            def exptype: TA = variables match {
//                case Nil => expression.exptype
//                case head::tail => ->(head.exptype, AbsN(tail, expression).exptype  )
//            }
//        }
//
//    implicit def convertAbsNToAbs(a: AbsN):Abs = a.variables match {
//        case head::tail => tail match {
//                case Nil => Abs(head, a.expression)
//                case _ => Abs(head,convertAbsNToAbs(AbsN(tail, a.expression)))
//        }
//        case Nil => throw new IllegalArgumentException("N-ary Abstraction cannot be converted to a standard abstraction when the list of variables is empty: "+a)
//    }
//
//    implicit def convertAbsToAbsN(a:Abs):AbsN =

    def AbsN(variables: List[Var], expression: LambdaExpression):LambdaExpression =
        if (!variables.isEmpty) (variables :\ expression)(Abs)
        else expression
    


    case class AppN(function: LambdaExpression, argument: LambdaExpression*) {
        val x = argument.toList(1)
    }

    def exportLambdaExpressionToString(expression: LambdaExpression):String = expression match {
        case Var(name,exptype) => name.toString
        case Abs(variable, exp) => "\\" + exportLambdaExpressionToString(variable) + "." + exportLambdaExpressionToString(exp)
        case App(function, argument) => "(" + exportLambdaExpressionToString(function) + " " + exportLambdaExpressionToString(argument)  + ")"
    }

    def exportLambdaExpressionToStringWithTypes(expression: LambdaExpression):String = expression match {
        case Abs(variable, exp) => "\\" + exportLambdaExpressionToString(variable) + "." + exportLambdaExpressionToString(exp)
        case App(function, argument) => "(" + exportLambdaExpressionToString(function) + " " + exportLambdaExpressionToString(argument)  + ")"
        case Var(name,exptype) => {
            name.toString +
                "ToDo"

        }
    }
}