/*
 * typedLambdaCalculus.scala
 *
 */

package at.logic.language.lambda

import symbols._
import symbols.ImplicitConverters._
import scala.collection.immutable._
import types._

package typedLambdaCalculus {

  trait LambdaFactoryProvider {
    def factory : LambdaFactoryA = LambdaFactory
  }

  trait LambdaExpression extends LambdaFactoryProvider {
    def exptype: TA
    def toString1(): String
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
    def toStringSimple: String
  }

  trait LambdaFactoryA {
    def createVar( name: SymbolA, exptype: TA ): Var = createVar(name, exptype, None)
    def createVar( name: SymbolA, exptype: TA, dbInd: Option[Int]) : Var
    def createAbs( variable: Var, exp: LambdaExpression ) : Abs
    def createApp( fun: LambdaExpression, arg: LambdaExpression ) : App
  }

  object LambdaFactory extends LambdaFactoryA {
    def createVar( name: SymbolA, exptype: TA, dbInd: Option[Int])  = new Var( name, exptype, dbInd )
    def createAbs( variable: Var, exp: LambdaExpression ) : Abs = new Abs( variable, exp )
    def createApp( fun: LambdaExpression, arg: LambdaExpression ) : App = new App( fun, arg )
  }

  class Var protected[typedLambdaCalculus]( val name: SymbolA, val exptype: TA,  dbInd: Option[Int]) extends LambdaExpression {
    private[lambda] val dbIndex: Option[Int] = dbInd // represents a bound variable and its de Bruijn index
    def this(name: SymbolA, exptype: TA) = this(name, exptype, None)
    // alpha equlas as ignores bound variable names
    override def equals(a: Any) = (a,dbIndex) match {
      case (s: Var, None) if s.isFree => (s.name == name && s.exptype == exptype) // a free variable can only be equal to another free variable
      case (s: Var, Some(dbi)) if s.isBound => (dbi == s.dbIndex.get && s.exptype == exptype) // a bound variable can only be equal to another bound variable
      case _ => false
    }
    override def hashCode() = exptype.hashCode
    override def toString() = "Var(" + toStringSimple() + "," + exptype + ")"
    def toString1(): String = name.toString
    // in curly brackets is the de bruijn index
    def toStringSimple() = name.toString + (if (isBound) """{""" + dbIndex.get + """}""" else "")
    def isFree = dbIndex == None
    def isBound = !isFree
  }
  // TODO: remove!?!
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

   class Abs protected[typedLambdaCalculus]( vari: Var, exp: LambdaExpression ) extends LambdaExpression  {
    val expression = createDeBruijnIndex(vari, exp, computeMaxDBIndex(exp)+1)
    val variable = vari.factory.createVar(vari.name, vari.exptype, Some(computeMaxDBIndex(exp)+1))  // set bounded variable index for given variable, must be done only after the index was alrewady set as otherwise the new var will be bound and the old ones not
    def exptype: TA = ->(variable.exptype,expression.exptype)
    override def equals(a: Any) = a match {
      case s: Abs => (s.variable == variable && s.expression == expression && s.exptype == exptype)
      case _ => false
    }
    override def hashCode() = exptype.hashCode
    override def toString() = "Abs(" + variable + "," + expression + ")"
    def toString1(): String = "Abs(" + variable.toString1 + "," + expression.toString1 + ")"
    def toStringSimple = "(λ" + variable.toStringSimple + "." + expression.toStringSimple + ")"
    private def createDeBruijnIndex(variable: Var, exp: LambdaExpression, nextDBIndex: Int): LambdaExpression = exp match {
      case v: Var if variable == v => v.factory.createVar(v.name, v.exptype, Some(nextDBIndex)) // also does not match if v is already a bound variable (with different dbindex) do to the Var equals method
      case v: Var => v
      case App(a, b) => App(createDeBruijnIndex(variable, a, nextDBIndex), createDeBruijnIndex(variable, b, nextDBIndex))
      case Abs(v, a) => if (variable == v)
        Abs(v, a) // in the case the inside bvar is the same do not replace index in it
        else Abs(v, createDeBruijnIndex(variable, a, nextDBIndex))
    }
    // returns the highest db index, returns 0 for no index. Based on the fact that outer abs has always a bigger index than inner one.
    private def computeMaxDBIndex(exp: LambdaExpression): Int = exp match {
      case App(x,y) => Math.max(computeMaxDBIndex(x), computeMaxDBIndex(y))
      case Abs(v,_) => v.dbIndex.get
      case _ => 0
    }
  }
  
  object Abs {
    def apply(variable: Var, expression: LambdaExpression) = expression.factory.createAbs(variable, expression)
    def unapply(expression: LambdaExpression) = expression match {
      case a: Abs => Some((a.variable, a.expression))
      case _ => None
    }
  }

  class App protected[typedLambdaCalculus]( val function: LambdaExpression, val argument: LambdaExpression ) extends LambdaExpression {
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
    def toString1(): String = "App(" + function.toString1+", "+argument.toString1+")"
    def toStringSimple() = "(" + function.toStringSimple + argument.toStringSimple + ")"
  }

  object App {
    def apply(function: LambdaExpression, argument: LambdaExpression) = function.factory.createApp( function, argument )
    def unapply(expression: LambdaExpression) = expression match {
      case a: App => Some((a.function, a.argument))
      case _ => None
    }
  }

  // when using AbsN it will match also for n=0 i.e. variables, constants, etc. so it must always be matched last
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
  // matches only if n > 0
  object AbsN1 {
    def unapply(expression: LambdaExpression):Option[(List[Var], LambdaExpression)] = expression match {
      case Abs(_,_) => AbsN.unapply(expression)
      case _ => None
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
  // matches only if n > 0
  object AppN1 {
    def unapply(expression: LambdaExpression):Option[(LambdaExpression, List[LambdaExpression])] = expression match {
      case App(_,_) => AppN.unapply(expression)
      case _ => None
    }
  }
  
  object IncreaseDBIndices {
    def apply(expression: LambdaExpression, indInc: Int): LambdaExpression = expression match {
      case v:Var if v.isBound => v.factory.createVar(v.name, v.exptype, Some(v.dbIndex.get+indInc))
      case App(m,n) => App(apply(m, indInc), apply(n, indInc))
      case Abs(v,m) => Abs(v.factory.createVar(v.name, v.exptype, Some(v.dbIndex.get+indInc)), apply(m, indInc))
      case _ => expression
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

  object exportLambdaExpressionToString {
    def apply(expression: LambdaExpression): String = expression match {
      case Var(name,exptype) => name.toString
      case Abs(variable, exp) => "\\" + exportLambdaExpressionToString(variable) + "." + exportLambdaExpressionToString(exp)
      case App(function, argument) => "(" + exportLambdaExpressionToString(function) + " " + exportLambdaExpressionToString(argument)  + ")"
    }
  }

  object exportLambdaExpressionToStringWithTypes {
    def apply(expression: LambdaExpression):String = expression match {
      case Abs(variable, exp) => "\\" + exportLambdaExpressionToString(variable) + "." + exportLambdaExpressionToString(exp)
      case App(function, argument) => "(" + exportLambdaExpressionToString(function) + " " + exportLambdaExpressionToString(argument)  + ")"
      case Var(name,exptype) => {
        name.toString +
          "ToDo"
      }
    }
  }
}
