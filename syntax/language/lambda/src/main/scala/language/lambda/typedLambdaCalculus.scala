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
    def syntaxEquals(e: LambdaExpression): Boolean
    def =^(e: LambdaExpression): Boolean = syntaxEquals(e)
    def getFreeAndBoundVariables():Tuple2[Set[Var],Set[Var]] = this match {
      case v: Var if v.isFree => (HashSet(v), new EmptySet)
      case v: Var => (new EmptySet, HashSet(v))
      case App(exp, arg) => {
        val mFBV = exp.getFreeAndBoundVariables()
        val nFBV = arg.getFreeAndBoundVariables()
        (mFBV._1 ++ nFBV._1, mFBV._2 ++ nFBV._2)
      }
      case Abs(v, exp) => {
        val mFBV = exp.getFreeAndBoundVariables()
        val bound = mFBV._2 + v
        (mFBV._1, bound)
      }
    }
    /*def getFreeAndBoundVariables():Tuple2[Set[Var],Set[Var]] = this match {
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
    }*/
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
    def syntaxEquals(e: LambdaExpression) = e match {
      case v: Var => (v.name == name && v.exptype == exptype)
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

  /*
   * There are two ways to view an abstraction with db indices. The physical way of the concatenataion of a variable and an expression
   * and the theoretical way of bindind the variable within the expression. In practice we need both versions:
   * - we need to be able to decompose an Abs so the specific variable in the expression is no longer bound in the subterm
   * - we need also to be able to inductively go over a term and know that a variable is bound up-somewhere.
   * Our solution to that is to have the default methods behave in the physical way. Decomposing an Abs return a free variable and
   * an expression with the variable unbound. We will also include a method that return the subterm together with the binding information.
   * the non-default methods will have the suffix InScope.
   */
   class Abs protected[typedLambdaCalculus](val variable: Var, val expression: LambdaExpression ) extends LambdaExpression  {
     require (variable.isFree)
    val expressionInScope = createDeBruijnIndex(variable, expression, computeMaxDBIndex(expression)+1)
    val variableInScope = variable.factory.createVar(variable.name, variable.exptype, Some(computeMaxDBIndex(expression)+1))  // set bounded variable index for given variable, must be done only after the index was alrewady set as otherwise the new var will be bound and the old ones not
    def exptype: TA = ->(variable.exptype,expression.exptype)
    override def equals(a: Any) = a match {
      case s: Abs => (s.variableInScope == variableInScope && s.expressionInScope == expressionInScope && s.exptype == exptype)
      case _ => false
    }
    def syntaxEquals(e: LambdaExpression) = e match {
      case AbsInScope(v,exp) => (v =^ variableInScope && exp =^ expressionInScope && e.exptype == exptype)
      case _ => false
    }
    override def hashCode() = exptype.hashCode
    override def toString() = "Abs(" + variableInScope + "," + expressionInScope + ")"
    def toString1(): String = "Abs(" + variableInScope.toString1 + "," + expressionInScope.toString1 + ")"
    def toStringSimple = "(λ" + variableInScope.toStringSimple + "." + expressionInScope.toStringSimple + ")"
    private def createDeBruijnIndex(vr: Var, exp: LambdaExpression, nextDBIndex: Int): LambdaExpression = exp match {
      case v: Var if vr =^ v => v.factory.createVar(v.name, v.exptype, Some(nextDBIndex)) // also does not match if v is already a bound variable (with different dbindex) do to the Var equals method
      case v: Var => v
      case v @ App(a, b) => App(createDeBruijnIndex(vr, a, nextDBIndex), createDeBruijnIndex(vr, b, nextDBIndex))
      /* In Abs we check if the nested abs does not have the same variable. As the creation of nested abs is inductive we might have
       * two nested abs where the index must be increased by 1. This will cause the nested abs to:
       * 1) if both nested and outer bvar name is equal then it will have the exact same bound variable as it will be increased by one
       * and in general will bound the appearances of the outer variable appearing within the nested abs. This is imposible as two abs
       * cannot have the same bound variable name if both also appears in the body of the nested abs. for example: \x.\x.xx . In the
       * example both variables in the nested will be bound only by the second x. To deal with that we recursively go into the nested
       * abs to increase the index of the variables only if the bound variables differs with regard to name.
       * 2) if they dont have the same name then as we compare indexed bvars also by their name, they will never be equal and there is
       * no danger of doing a mistake here.
       */
      case abs: Abs => if (vr =^ abs.variable)
        abs // in the case the inside bvar is the same do not replace index in it
        else Abs(abs.variable, createDeBruijnIndex(vr, abs.expression, nextDBIndex))
    }
    // returns the highest db index, returns 0 for no index. Based on the fact that outer abs has always a bigger index than inner one.
    private def computeMaxDBIndex(exp: LambdaExpression): Int = exp match {
      case App(x,y) => Math.max(computeMaxDBIndex(x), computeMaxDBIndex(y))
      case AbsInScope(v,_) => v.dbIndex.get
      case _ => 0
    }
  }

  /*
   * This extractor decompose an Abs to its two arguments without the extra bninding information added in Abs constructor
   */
  object Abs {
    def apply(variable: Var, expression: LambdaExpression) = expression.factory.createAbs(variable, expression)
    def unapply(expression: LambdaExpression) = expression match {
      case a: Abs => Some((a.variable, a.expression))
      case _ => None
    }
  }

  /*
   * This extractor contains the binding information in the variable and in the expression
   */
  object AbsInScope {
    def unapply(expression: LambdaExpression) = expression match {
      case a: Abs => Some((a.variableInScope, a.expressionInScope))
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
    def syntaxEquals(e: LambdaExpression) = e match {
      case App(a,b) => (a =^ function && b =^ argument && e.exptype == exptype)
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
      case AbsInScope(variable, exp) => "\\" + exportLambdaExpressionToString(variable) + "." + exportLambdaExpressionToString(exp)
      case App(function, argument) => "(" + exportLambdaExpressionToString(function) + " " + exportLambdaExpressionToString(argument)  + ")"
    }
  }

  object exportLambdaExpressionToStringWithTypes {
    def apply(expression: LambdaExpression):String = expression match {
      case AbsInScope(variable, exp) => "\\" + exportLambdaExpressionToString(variable) + "." + exportLambdaExpressionToString(exp)
      case App(function, argument) => "(" + exportLambdaExpressionToString(function) + " " + exportLambdaExpressionToString(argument)  + ")"
      case Var(name,exptype) => {
        name.toString +
          "ToDo"
      }
    }
  }
}
