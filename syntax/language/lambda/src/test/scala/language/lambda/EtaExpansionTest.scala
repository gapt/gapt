package at.logic.language.lambda

import etaExpansion. {EtaNormalize, EtaExpand}
import org.specs.SpecificationWithJUnit
import typedLambdaCalculus._
import types.Definitions._
import symbols._
import symbols.ImplicitConverters._
import types. {Ti, ->}

/**
 * Created by IntelliJ IDEA.
 * User: cdunchev
 * Date: 10/24/10
 * Time: 2:28 AM
 * To change this template use File | Settings | File Templates.
 */

class EtaExpansionTest extends SpecificationWithJUnit {
  val v = Var("v", i, LambdaFactory);
  val x = Var("x", i, LambdaFactory);
  val y = Var("y", i, LambdaFactory);
  val z = Var("z", i, LambdaFactory);
  val f = Var("f", i -> i, LambdaFactory);
  val g = Var("g", i -> i, LambdaFactory)
  val f2 = Var("f2", i -> i, LambdaFactory);
  val g2 = Var("g2", i -> i, LambdaFactory)
  val g3 = Var("g3", ->(Ti(),->(Ti(),Ti())), LambdaFactory)
  val g4 = Abs(x,g3)
  val g5 = Abs(x,App(g3,x))
  val g6 = Var("g6", ->(->(Ti(),Ti()),->(Ti(),Ti())), LambdaFactory)
  "EtaExpansion" should {
    "expand correctly the lambda expressions f : (i->i) to lambda x. f(x)" in {
      etaExpansion.EtaExpand(f)(disAllowedVars = EtaExpand.disAllowedVars) must beEqual (Abs(x,App(f,x)))
//      println("\n\ntype = "+g5.exptype.toString)
//      println("\n\neta : "+EtaExpand(f).toString1+"\n\n")
//      println("\n\neta : "+etaExpansion.EtaExpand(g4).toString1+"\n\n")
    //  println("\n\neta : "+EtaExpand(g5).toString1+"\n\n")
//      0 must beEqual (0)
    }
    "expand correctly the lambda expressions g3(x) : (i->i) to lambda y. g3(x,y)" in {
//      etaExpansion.EtaExpand(g3) must beEqual (Abs(y,Abs(x, App(g3,x))))
//      println("\n\ntype = "+g5.exptype.toString)
//      println("\n\neta : "+EtaExpand(App(g3,x))(disAllowedVars = EtaExpand.disAllowedVars).toString1+"\n\n")
      EtaExpand(App(g3,x))(disAllowedVars = EtaExpand.disAllowedVars) must beEqual (Abs(y, AppN(g3, x.asInstanceOf[LambdaExpression]::y.asInstanceOf[LambdaExpression]::Nil)))
//      println("\n\neta : "+etaExpansion.EtaExpand(g4).toString1+"\n\n")
//      println("\n\neta : "+etaExpansion.EtaExpand(g5).toString1+"\n\n")
//      0 must beEqual (0)
    }
    "expand correctly the lambda expressions g3 : i->(i->i) to lambda x,y. g3(x,y)" in {
//      etaExpansion.EtaExpand(g3) must beEqual (Abs(y,Abs(x, App(g3,x))))
//      println("\n\ntype = "+g5.exptype.toString)
//      println("\n\neta : "+EtaExpand(g3)(disAllowedVars = EtaExpand.disAllowedVars).toString1+"\n\n")
      EtaExpand(g3)(disAllowedVars = EtaExpand.disAllowedVars) must beEqual (AbsN(x::y::Nil, AppN(g3,x::y::Nil)))
//      println("\n\neta : "+etaExpansion.EtaExpand(g4).toString1+"\n\n")
//      println("\n\neta : "+etaExpansion.EtaExpand(g5).toString1+"\n\n")
//      0 must beEqual (0)
    }
    "expand correctly the lambda expressions g3(g3(x,y)) : i to lambda z. g3(g3(x,y),z)" in {
//      etaExpansion.EtaExpand(g3) must beEqual (Abs(y,Abs(x, App(g3,x))))
//      println("\n\ntype = "+g5.exptype.toString)
//      println("\n\neta : "+EtaExpand(App(g3, AppN(g3,x::y::Nil)))(disAllowedVars = EtaExpand.disAllowedVars).toString1+"\n\n")
      EtaExpand(App(g3, AppN(g3,x::y::Nil)))(disAllowedVars = EtaExpand.disAllowedVars) must beEqual (Abs(z, AppN(g3, AppN(g3, x::y::Nil)::z::Nil)))
//      println("\n\neta : "+etaExpansion.EtaExpand(g4).toString1+"\n\n")
//      println("\n\neta : "+etaExpansion.EtaExpand(g5).toString1+"\n\n")
//      0 must beEqual (0)
    }
    "expand correctly the lambda expressions g6(f) : (i->i) to eta Abs(#7,App(App(g6, Abs(#8,App(f, #8))), #7))" in {
//      etaExpansion.EtaExpand(g3) must beEqual (Abs(y,Abs(x, App(g3,x))))
//      println("\n\ntype = "+g5.exptype.toString)
//      println("\n\neta : "+EtaExpand(App(g6,f))(EtaExpand.disAllowedVars).toStringSimple+"\n\n")
      EtaExpand(App(g6,f))(EtaExpand.disAllowedVars) must beEqual (Abs(z,App(App(g6, Abs(x,App(f, x))), z)))
//      println("\n\neta : "+etaExpansion.EtaExpand(g4).toString1+"\n\n")
//      println("\n\neta : "+etaExpansion.EtaExpand(g5).toString1+"\n\n")
//      0 must beEqual (0)
    }
    "expand correctly the lambda expressions g6 : (i->i)->(i->i) to lambda x,y. g6(lambda z. x(z),y)" in {
//      etaExpansion.EtaExpand(g3) must beEqual (Abs(y,Abs(x, App(g3,x))))
//      println("\n\ntype = "+g5.exptype.toString)
//      println("\n\neta : "+EtaExpand(g6)(disAllowedVars = EtaExpand.disAllowedVars).toString1+"\n\n")
      EtaExpand(g6)(disAllowedVars = EtaExpand.disAllowedVars) must beEqual (AbsN(f::y::Nil, AppN(g6, Abs(z,App(f,z))::y::Nil)))
//      println("\n\neta : "+etaExpansion.EtaExpand(g4).toString1+"\n\n")
//      println("\n\neta : "+etaExpansion.EtaExpand(g5).toString1+"\n\n")
//      0 must beEqual (0)
    }

    "expand correctly the lambda expressions f : (i->i) to f2 : (i->i)" in {
//      etaExpansion.EtaExpand(g3) must beEqual (Abs(y,Abs(x, App(g3,x))))
//      println("\n\ntype = "+g5.exptype.toString)
//      println("\n\neta : "+EtaExpand(f)(disAllowedVars = EtaExpand.disAllowedVars).toString1+"\n\n")
//      println("\n\neta : "+EtaExpand(Abs(x,App(g3,x)))(disAllowedVars = EtaExpand.disAllowedVars).toString1+"\n\n")
      val v2 = EtaExpand(Abs(x,App(g3,x)))(disAllowedVars = EtaExpand.disAllowedVars)
      EtaExpand(g3)(disAllowedVars = EtaExpand.disAllowedVars) must beEqual (v2)// (EtaExpand(f2)(disAllowedVars = EtaExpand.disAllowedVars))
//      println("\n\neta : "+etaExpansion.EtaExpand(g4).toString1+"\n\n")
//      println("\n\neta : "+etaExpansion.EtaExpand(g5).toString1+"\n\n")
//      0 must beEqual (0)
    }


  }

}