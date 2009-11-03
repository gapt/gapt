/*
 * typedLambdaCalculus.scala
 *
 */

package at.logic.language

import Symbols._
import Symbols.SymbolImplicitConverters._
import scala.collection.immutable._

object TypedLambdaCalculus {

    import at.logic.language.Types._
     
    abstract class LambdaExpression {
        def exptype: TA

        def getFreeAndBoundVariables():Tuple2[Set[Var],Set[Var]] = this match {
            case v: Var => (HashSet(v),  new EmptySet )
            case App(m,n) => {
                    val mFBV = m.getFreeAndBoundVariables()
                    val nFBV = n.getFreeAndBoundVariables()
                    (mFBV._1 ++ nFBV._1, mFBV._2 ++ nFBV._2)
            }
            case Abs(x,m) => {
                    val mFBV = m.getFreeAndBoundVariables()
                    val bound = mFBV._2 + x
                    val free = mFBV._1 - x
                    (free, bound)
            }
        }
    }

    case class Var(val name: SymbolA, val exptype: TA ) extends LambdaExpression

    /*
        Definition of Abs
    */
    class Abs (val variable: Var, val expression: LambdaExpression) extends LambdaExpression  {
        def exptype: TA = ->(variable.exptype,expression.exptype)
        override def equals(a: Any) = a match {
            case s: Abs => (s.variable == variable && s.expression == expression && s.exptype == exptype)
            case _ => false
        }
        override def hashCode() = exptype.hashCode
        override def toString() = "(" + variable + "," + expression + ")"
    }
    object Abs {
        def apply[T <: LambdaExpression](variable: Var, expression: T)(implicit factory: AbsFactory[T]) = factory.create(variable, expression)
        def unapply(expression: LambdaExpression) = expression match {
            case a: Abs => Some((a.variable, a.expression))
            case _ => None
        }
    }
    trait AbsFactory[T <: LambdaExpression] {
        def create (variable: Var, expression: T): Abs
    }
    implicit object LambdaExpressionAbsFactory extends AbsFactory[LambdaExpression] {
        def create (variable: Var, expression: LambdaExpression) = new Abs(variable, expression)
    }
    implicit object VarAbsFactory extends AbsFactory[Var] {
        def create (variable: Var, expression: Var) = new Abs(variable, expression)
    }
    implicit object AppAbsFactory extends AbsFactory[App] {
        def create (variable: Var, expression: App) =  new Abs(variable, expression)
    }
    implicit object AbsAbsFactory extends AbsFactory[Abs] {
        def create (variable: Var, expression: Abs) = new Abs(variable, expression)
    }
    object AbsN {
        def apply[T <: LambdaExpression](variables: List[Var], expression: T)(implicit factory: AbsFactory[T]): LambdaExpression = variables match {
            case Nil => expression
            case x::ls => Abs(x, apply(ls, expression))
        }
        /*def apply(variables: List[Var], expression: LambdaExpression) = if (!variables.isEmpty) (variables :\ expression)(Abs)
                                                                        else expression*/
        def unapply(expression: LambdaExpression):Option[(List[Var], LambdaExpression)] = Some(unapplyRec(expression))
        def unapplyRec(expression: LambdaExpression): (List[Var], LambdaExpression) = expression match {
            case Abs(v,exp) => (v :: unapplyRec(exp)._1, unapplyRec(exp)._2 )
            case v: Var => (Nil, v)
            case a: App => (Nil, a)
        }
    }
    /* end of App */

    /*
        Definition of App
    */
    class App (val function: LambdaExpression, val argument: LambdaExpression) extends LambdaExpression {
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
        override def toString() = "(" + function + "," + argument + ")"
    }

    object App {
        def apply[T <: LambdaExpression](function: T, argument: LambdaExpression)(implicit factory: AppFactory[T]) = factory.create(function, argument)
        def unapply(expression: LambdaExpression) = expression match {
            case a: App => Some((a.function, a.argument))
            case _ => None
        }
    }
    trait AppFactory[T <: LambdaExpression] {
        def create (function: T, argument: LambdaExpression): App
    }
    implicit object LambdaExpressionAppFactory extends AppFactory[LambdaExpression] {
        def create (function: LambdaExpression, argument: LambdaExpression) = new App(function, argument)
    }
    implicit object VarAppFactory extends AppFactory[Var] {
        def create (function: Var, argument: LambdaExpression) = new App(function, argument)
    }
    implicit object AppAppFactory extends AppFactory[App] {
        def create (function: App, argument: LambdaExpression) = new App(function, argument)
    }
    implicit object AbsAppFactory extends AppFactory[Abs] {
        def create (function: Abs, argument: LambdaExpression) = new App(function, argument)
    }
    object AppN {
        def apply[T <: LambdaExpression](function: T, arguments:List[LambdaExpression])(implicit factory: AppFactory[T]): LambdaExpression = arguments match {
            case Nil => function
            case x::ls => apply(App(function, x), ls)
        }
    /*if (!arguments.isEmpty) (function /: arguments)(App(factory))
                                                                                  else function*/
        def unapply(expression: LambdaExpression):Option[(LambdaExpression, List[LambdaExpression])] = Some(unapplyRec(expression))
        def unapplyRec(expression: LambdaExpression):(LambdaExpression, List[LambdaExpression]) = expression match {
            case App(f,arg) => (unapplyRec(f)._1, unapplyRec(f)._2 ::: (arg::Nil) )
            case v: Var => (v,Nil)
            case a: Abs => (a,Nil)
        }
    }
    /* end of App */

    object freshVar {
        def apply(exptype: TA, disallowedVariables: Set[Var]):Var = {
            var counter = 1
            var v = new Var("#"+counter, exptype)
            while (disallowedVariables.contains(v)) {
                counter += 1
                v = new Var("#"+counter, exptype)
            }
            v
        }
        def apply(exptype: TA, context: LambdaExpression):Var = {
            val (cFV, cBV) = context.getFreeAndBoundVariables
            apply(exptype, cFV ++ cBV)
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