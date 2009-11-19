/*
 * typedLambdaCalculus.scala
 *
 */

package at.logic.language.lambda

import Symbols._
import Symbols.SymbolImplicitConverters._
import scala.collection.immutable._
import Types._

object TypedLambdaCalculus {

    trait LambdaExpression {
        def exptype: TA
        private[TypedLambdaCalculus] val factory: LambdaFactoryA
        def getFreeAndBoundVariables():Tuple2[Set[Var],Set[Var]] = this match {
            case v: Var => (HashSet(v), new EmptySet)
            case app: App => {
                    val mFBV = app.function.getFreeAndBoundVariables()
                    val nFBV = app.argument.getFreeAndBoundVariables()
                    (mFBV._1 ++ nFBV._1, mFBV._2 ++ nFBV._2)
            }
            case abs: Abs => {
                    val mFBV = abs.expression.getFreeAndBoundVariables()
                    //val bound = mFBV._2 + x
                    //val free = mFBV._1 - x
                    val bound = mFBV._2 + abs.variable
                    val free = mFBV._1.filter(y => abs.variable != y)
                    (free, bound)
            }
        }
    }

    trait LambdaFactoryA {
        def createVar( name: SymbolA, exptype: TA ) : Var
        def createAbs( variable: Var, exp: LambdaExpression ) : Abs
        def createApp( fun: LambdaExpression, arg: LambdaExpression ) : App
    }

    object LambdaFactory extends LambdaFactoryA {
        def createVar( name: SymbolA, exptype: TA ) : Var = new Var( name, exptype, this )
        def createAbs( variable: Var, exp: LambdaExpression ) : Abs = new Abs( variable, exp, this )
        def createApp( fun: LambdaExpression, arg: LambdaExpression ) : App = new App( fun, arg, this )
    }

    class Var protected[TypedLambdaCalculus]( val name: SymbolA, val exptype: TA, val factory: LambdaFactoryA) extends LambdaExpression {
        override def equals(a: Any) = a match {
            case s: Var => (s.name == name && s.exptype == exptype)
            case _ => false
        }
        override def hashCode() = exptype.hashCode
        override def toString() = "Var(" + name + "," + exptype + ")"
    }
    object LambdaVar {
        def apply(name: SymbolA, exptype: TA) = Var(name, exptype, LambdaFactory)
    }

    object Var {
        def apply(name: SymbolA, exptype: TA, factory: LambdaFactoryA) = factory.createVar(name, exptype)
        def unapply(expression: LambdaExpression) = expression match {
        case a: Var => Some((a.name, a.exptype))
        case _ => None
        }
    }

    class Abs protected[TypedLambdaCalculus]( val variable: Var, val expression: LambdaExpression, val factory: LambdaFactoryA ) extends LambdaExpression  {
        def exptype: TA = ->(variable.exptype,expression.exptype)
        override def equals(a: Any) = a match {
            case s: Abs => (s.variable == variable && s.expression == expression && s.exptype == exptype)
            case _ => false
        }
        override def hashCode() = exptype.hashCode
        override def toString() = "Abs(" + variable + "," + expression + ")"
    }

    object Abs {
        def apply(variable: Var, expression: LambdaExpression) = expression.factory.createAbs(variable, expression)
        def unapply(expression: LambdaExpression) = expression match {
            case a: Abs => Some((a.variable, a.expression))
            case _ => None
        }
    }

    class App protected[TypedLambdaCalculus]( val function: LambdaExpression, val argument: LambdaExpression, val factory: LambdaFactoryA) extends LambdaExpression {
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
        override def equals(a: Any) = a match {
            case s: App => (s.function == function && s.argument == argument && s.exptype == exptype)
            case _ => false
        }
        override def hashCode() = exptype.hashCode
        override def toString() = "App(" + function + "," + argument + ")"
    }

    object App {
        def apply(function: LambdaExpression, argument: LambdaExpression) = function.factory.createApp( function, argument )
        def unapply(expression: LambdaExpression) = expression match {
            case a: App => Some((a.function, a.argument))
            case _ => None
        }
    }

    object AbsN {
        def apply(variables: List[Var], expression: LambdaExpression): LambdaExpression = variables match {
            case Nil => expression
            case x::ls => Abs(x, apply(ls, expression))
        }
        /*def apply(variables: List[Var], expression: LambdaExpression) = if (!variables.isEmpty) (variables :\ expression)(Abs)
                                                                        else expression*/
        def unapply(expression: LambdaExpression):Option[(List[Var], LambdaExpression)] = Some(unapplyRec(expression))
        def unapplyRec(expression: LambdaExpression): (List[Var], LambdaExpression) = expression match {
            case Abs(v, e) => {val t = unapplyRec(e); (v :: t._1, t._2 )}
            case v: Var => (Nil, v)
            case a: App => (Nil, a)
        }
    }

    object AppN {
        def apply(function: LambdaExpression, arguments:List[LambdaExpression]): LambdaExpression = arguments match {
            case Nil => function
            case x::ls => apply(App(function, x), ls)
        }
        def unapply(expression: LambdaExpression):Option[(LambdaExpression, List[LambdaExpression])] = Some(unapplyRec(expression))
        def unapplyRec(expression: LambdaExpression):(LambdaExpression, List[LambdaExpression]) = expression match {
            case App(f, arg) => {val t = unapplyRec(f); (t._1, t._2 ::: (arg::Nil)) }
            case v: Var => (v,Nil)
            case a: Abs => (a,Nil)
        }
    }

    object freshVar {
        def apply(exptype: TA, disallowedVariables: Set[Var], dummy: LambdaExpression) :Var = {
            var counter = 1
            var v = Var("#"+counter, exptype,dummy.factory)
            while (disallowedVariables.contains(v)) {
                counter += 1
                v = Var("#"+counter, exptype,dummy.factory)
            }
            v
        }
        def apply(exptype: TA, context: LambdaExpression, dummy: LambdaExpression) :Var = {
            val (cFV, cBV) = context.getFreeAndBoundVariables
            apply(exptype, cFV ++ cBV, dummy)
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