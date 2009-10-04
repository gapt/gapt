/*
 * typedLambdaCalculus.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language

object TypedLambdaCalculus {

    import at.logic.language.Types._
    
    abstract class SymbolA

    case class StringSymbol(string: String) extends SymbolA {
        override def toString = string
    }
    object StringSymbolImplicitConverters {
        implicit def toStringSymbol(s: String) = StringSymbol(s)
    }

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