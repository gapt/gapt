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
    
    abstract class LambdaExpression[+A <: Lambda] {
        def exptype: TA

        // all variables must be of the same level
        // The casting in the body of the function is required because we assume different elements are parameterized over A but as all variables must be of the same Athere is no problem.
        // TODO change List into a covariant Set
        def getFreeAndBoundVariables():Tuple2[List[Var[A]],List[Var[A]]] = this match {
            case v: Var[_] => (v::Nil,  Nil )
            case app: App[_] => {
                    val mFBV = app.function.getFreeAndBoundVariables()
                    val nFBV = app.argument.getFreeAndBoundVariables()
                    (mFBV._1 ++ nFBV._1, mFBV._2 ++ nFBV._2)
            }
            case abs: Abs[_] => {
                    val mFBV = abs.expression.getFreeAndBoundVariables()
                    //val bound = mFBV._2 + x
                    //val free = mFBV._1 - x
                    val bound = abs.variable::mFBV._2
                    val free = mFBV._1.filter(y => abs.variable != y)
                    (free, bound)
            }
        }
    }

    trait Lambda

    /*
        Definition of Var
    */
    class Var[+A <: Lambda](val name: SymbolA, val exptype: TA ) extends LambdaExpression[A] {
        override def equals(a: Any) = a match {
            case s: Var[_] => (s.name == name && s.exptype == exptype)
            case _ => false
        }
        override def hashCode() = exptype.hashCode
        override def toString() = "(" + name + "," + exptype + ")"
    }
    object Var {
        def apply[A <: Lambda](name: SymbolA, exptype: TA)(implicit factory: VarFactory[A]) = factory.create(name, exptype)
        // this apply is used to create a Var of specific type implicitly
        def apply[A <: Lambda](name: SymbolA, exptype: TA, dummy: LambdaExpression[A])(implicit factory: VarFactory[A]) = factory.create(name, exptype)
        def unapply(expression: LambdaExpression[Lambda]) = expression match {
            case a: Var[_] => Some((a.name, a.exptype))
            case _ => None
        }
    }
    trait VarFactory[A <: Lambda] {
        def create (name: SymbolA, exptype: TA): Var[A]
    }
    implicit object LambdaVarFactory extends VarFactory[Lambda] {
        def create (name: SymbolA, exptype: TA) = new Var[Lambda](name, exptype)
    }
    /* end of Var */

    /*
        Definition of Abs
    */
    class Abs[+A <: Lambda] (val variable: Var[A], val expression: LambdaExpression[A]) extends LambdaExpression[A]  {
        def exptype: TA = ->(variable.exptype,expression.exptype)
        override def equals(a: Any) = a match {
            case s: Abs[_] => (s.variable == variable && s.expression == expression && s.exptype == exptype)
            case _ => false
        }
        override def hashCode() = exptype.hashCode
        override def toString() = "(" + variable + "," + expression + ")"
    }
    object Abs {
        def apply[A <: Lambda](variable: Var[A], expression: LambdaExpression[A])(implicit factory: AbsFactory[A]) = factory.create(variable, expression)
        def unapply(expression: LambdaExpression[Lambda]) = expression match {
            case a: Abs[_] => Some((a.variable, a.expression))
            case _ => None
        }
    }
    trait AbsFactory[A <: Lambda] {
        def create (variable: Var[A], expression: LambdaExpression[A]): Abs[A]
    }
    implicit object LambdaAbsFactory extends AbsFactory[Lambda] {
        def create (variable: Var[Lambda], expression: LambdaExpression[Lambda]) = new Abs[Lambda](variable, expression)
    }
    object AbsN {
        def apply[A <: Lambda](variables: List[Var[A]], expression: LambdaExpression[A])(implicit factory: AbsFactory[A]): LambdaExpression[A] = variables match {
            case Nil => expression
            case x::ls => Abs(x, apply(ls, expression))
        }
        /*def apply(variables: List[Var], expression: LambdaExpression) = if (!variables.isEmpty) (variables :\ expression)(Abs)
                                                                        else expression*/
        def unapply(expression: LambdaExpression[Lambda]):Option[(List[Var[Lambda]], LambdaExpression[Lambda])] = Some(unapplyRec(expression))
        def unapplyRec(expression: LambdaExpression[Lambda]): (List[Var[Lambda]], LambdaExpression[Lambda]) = expression match {
            case Abs(v, e) => {val t = unapplyRec(e); (v :: t._1, t._2 )}
            case v: Var[_] => (Nil, v)
            case a: App[_] => (Nil, a)
        }
    }
    /* end of App */

    /*
        Definition of App
    */
    class App[+A <: Lambda] (val function: LambdaExpression[A], val argument: LambdaExpression[A]) extends LambdaExpression[A] {
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
            case s: App[_] => (s.function == function && s.argument == argument && s.exptype == exptype)
            case _ => false
        }
        override def hashCode() = exptype.hashCode
        override def toString() = "(" + function + "," + argument + ")"
    }

    object App {
        def apply[A <: Lambda](function: LambdaExpression[A], argument: LambdaExpression[A])(implicit factory: AppFactory[A]) = factory.create(function, argument)
        def unapply(expression: LambdaExpression[Lambda]) = expression match {
            case a: App[_] => Some((a.function, a.argument))
            case _ => None
        }
    }
    trait AppFactory[A <: Lambda] {
        def create (function: LambdaExpression[A], argument: LambdaExpression[A]): App[A]
    }
    implicit object LambdaAppFactory extends AppFactory[Lambda] {
        def create (function: LambdaExpression[Lambda], argument: LambdaExpression[Lambda]) = new App[Lambda](function, argument)
    }
   
    object AppN {
        def apply[A <: Lambda](function: LambdaExpression[A], arguments:List[LambdaExpression[A]])(implicit factory: AppFactory[A]): LambdaExpression[A] = arguments match {
            case Nil => function
            case x::ls => apply(App(function, x), ls)
        }
    /*if (!arguments.isEmpty) (function /: arguments)(App(factory))
                                                                                  else function*/
        def unapply(expression: LambdaExpression[Lambda]):Option[(LambdaExpression[Lambda], List[LambdaExpression[Lambda]])] = Some(unapplyRec(expression))
        def unapplyRec(expression: LambdaExpression[Lambda]):(LambdaExpression[Lambda], List[LambdaExpression[Lambda]]) = expression match {
            case App(f, arg) => {val t = unapplyRec(f); (t._1, t._2 ::: (arg::Nil)) }
            case v: Var[_] => (v,Nil)
            case a: Abs[_] => (a,Nil)
        }
    }
    /* end of App */

    object freshVar {
        def apply[A <: Lambda](exptype: TA, disallowedVariables: List[Var[A]])(implicit factory: VarFactory[A]) :Var[A] = {
            var counter = 1
            var v = Var[A]("#"+counter, exptype)
            while (disallowedVariables.contains(v)) {
                counter += 1
                v = Var[A]("#"+counter, exptype)
            }
            v
        }
        def apply[A <: Lambda](exptype: TA, context: LambdaExpression[A])(implicit factory: VarFactory[A]) :Var[A] = {
            val (cFV, cBV) = context.getFreeAndBoundVariables
            apply(exptype, cFV ++ cBV)
        }
    }

    def exportLambdaExpressionToString(expression: LambdaExpression[Lambda]):String = expression match {
        case Var(name,exptype) => name.toString
        case Abs(variable, exp) => "\\" + exportLambdaExpressionToString(variable) + "." + exportLambdaExpressionToString(exp)
        case App(function, argument) => "(" + exportLambdaExpressionToString(function) + " " + exportLambdaExpressionToString(argument)  + ")"
    }

    def exportLambdaExpressionToStringWithTypes(expression: LambdaExpression[Lambda]):String = expression match {
        case Abs(variable, exp) => "\\" + exportLambdaExpressionToString(variable) + "." + exportLambdaExpressionToString(exp)
        case App(function, argument) => "(" + exportLambdaExpressionToString(function) + " " + exportLambdaExpressionToString(argument)  + ")"
        case Var(name,exptype) => {
            name.toString +
                "ToDo"

        }
    }
}