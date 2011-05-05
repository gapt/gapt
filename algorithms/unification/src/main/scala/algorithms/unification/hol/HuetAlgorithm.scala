/*
 * HuetAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.unification.hol


import at.logic.utils.executionModels.searchAlgorithms.BFSAlgorithm
import at.logic.language.lambda.types. {->, Ti, TA, FunctionType}
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.algorithms.unification.UnificationAlgorithm
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.etaExpansion.EtaExpand
import scala.collection.mutable.Set
import at.logic.utils.executionModels.ndStream.{NDStream, Configuration}

import at.logic.language.lambda.BetaReduction._
import at.logic.language.lambda.BetaReduction

//import at.logic.language.lambda
  import StrategyOuterInner._
  import StrategyLeftRight._

class ConfigurationNode(val uproblems : List[Pair[HOLExpression, HOLExpression]], val subList : List[Pair[HOLExpression, HOLExpression]]) extends Configuration[Substitution[HOLExpression]] {


//  override def toString = "( "+uproblems.toString+" ; "+subList.toString+" )"
  override def toString = "( "+uproblems.map(x => (x._1.toStringSimple, x._2.toStringSimple))+" ; "+subList.map(x=> Pair(x._1.toString, x._2.toString)).toString+" )"

  def isTerminal: Boolean = uproblems match {
    case List() => true
    case _ => false
  }

  def result: Option[Substitution[HOLExpression]] = uproblems match {
    case List() => Some(Substitution[HOLExpression](subList.map( x => (x._1.asInstanceOf[HOLVar],x._2) )))
    case _ => None
  }

  def transformation1: ConfigurationNode = {
    new ConfigurationNode(uproblems.tail, subList)
  }

  def transformation2:  ConfigurationNode = {
    uproblems match {
      case (AbsN(varList1, Function(sym1 : ConstantStringSymbol, args1, returnType1)),AbsN(varList2, Function(sym2 : ConstantStringSymbol, args2, returnType2)))::s => {
          new ConfigurationNode((args1.map(x => AbsN(varList1,x)).zip(args2.map(x => AbsN(varList2,x)))).asInstanceOf[List[Pair[HOLExpression,HOLExpression]]]:::uproblems.tail, subList)
      }
    }
  }
// 4 a
  def transformation4a(uprobl : List[Pair[HOLExpression, HOLExpression]])(implicit disAllowedVars: Set[Var] ) :  ConfigurationNode = {
    uprobl match {
      case (AbsN(varList1, AppN(funcVar: HOLVar, args1)), AbsN(varList2, Function(sym : ConstantStringSymbol, args2, returnType)))::s => {
//            println("\nrule (4'a)\n")
            val dv  = disAllowedVars.foldLeft(scala.collection.immutable.Set[Var]())((ls,x) => ls.+(x))
  //                println("\n\n"+disAllowedVars.toString)
  //                val fv = freshVar(z, dv, x); disAllowedVars += fv; fv
            val newVarList = args1.map(x => {val fv = freshVar.apply1(x.exptype, dv, funcVar); disAllowedVars+=fv; fv} )
//            println("\n222    disAllowedVars : +"+disAllowedVars.toString+"\n")
//            println("\n222    newVarList : +"+newVarList.toString+"\n")
            val generalFlexibleTermList = args2.map(x1 => HuetAlgorithm.createFuncVarH(newVarList.asInstanceOf[List[HOLVar]], HuetAlgorithm.getListOfZs(x1.exptype)))
//            println("\n333  newVarList : " +newVarList.toString+      "          generalFlexibleTermList : "+generalFlexibleTermList.toString+" \n")

            val zHlist = generalFlexibleTermList.zip(args2.map(x => HuetAlgorithm.getListOfZs(x.exptype))).map(x => AbsN(x._2, x._1))
//            println("\n444\n"+zHlist.toString)


            val appzHlist = zHlist.map(x => {
  //              EtaExpand.s = (EtaExpand.s).union(disAllowedVars);
  //              val dum = EtaExpand.apply( AppN(x, newVarList))

              val ev = EtaExpand.apply( AppN(x, newVarList));
              disAllowedVars.union(ev.getFreeAndBoundVariables._1);
              disAllowedVars.union(ev.getFreeAndBoundVariables._2);
//              println("\n4444555   "+ disAllowedVars.toString +"\n")
              ev
            })

            val headType = FunctionType(returnType, args2.map(arg => arg.exptype))      //before returnType was the type of the head
            val term = AppN(Var(sym, headType,funcVar.factory), appzHlist)
//            println("\n555   "  + term.toString1+ " \n")
            val part_bind_t = AbsN(newVarList, term ).asInstanceOf[HOLExpression]
//            println("\n666 binding = "+ part_bind_t.toString1 +" \n")

            val sigma = Substitution[HOLExpression](funcVar, part_bind_t)

//            println("\n(4'a) end :\n"+(Tuple2(HuetAlgorithm.applySubToListOfPairs(conf.currentConf._1.tail,sigma), (funcVar,part_bind_t)::HuetAlgorithm.applySubToListOfPairs(conf.currentConf._2,sigma))).toString+"\n")

//            new ConfigurationNode(HuetAlgorithm.applySubToListOfPairs(uprobl.tail,sigma), (funcVar,part_bind_t)::HuetAlgorithm.applySubToListOfPairs(subList,sigma))

//            val newConfNode = new ConfigurationNode((HuetAlgorithm.applySubToListOfPairs((uprobl.head._1,uprobl.head._2)::uprobl.tail, sigma)).map(x => (x._1, BetaReduction.betaNormalize(x._2 )(Outermost)).asInstanceOf[Pair[HOLExpression, HOLExpression]]) ,
//              (funcVar,part_bind_t)::HuetAlgorithm.applySubToListOfPairs(subList,sigma))

            val newConfNode = new ConfigurationNode((HuetAlgorithm.applySubToListOfPairs(uprobl, sigma)).map(x => (x._1, BetaReduction.betaNormalize(x._2 )(Outermost)).asInstanceOf[Pair[HOLExpression, HOLExpression]]) ,
              (funcVar,part_bind_t)::HuetAlgorithm.applySubToListOfPairs(subList,sigma))


//            println("\nl:+  "+(new ConfigurationNode(Tuple2(HuetAlgorithm.applySubToListOfPairs(conf.currentConf._1.tail,sigma), (funcVar,part_bind_t)::HuetAlgorithm.applySubToListOfPairs(conf.currentConf._2,sigma))))).toString()
//            println("\n 4a, newConfNode = "+newConfNode.toString)
            newConfNode
//            println("\nrule 4a,  l:+ = "+l.toString)
          }
//          case _ => println("\nError in 4a\n")
        }
  }
// (g(#3(f(a:i):i):i, #5(f(a:i):i):i):i, g(f(g(#3(a:i):i, #5(a:i):i):i):i, f(((λ#1:i.g(#3(#1:i):i, #5(#1:i):i):i))(a:i)):i):i) ; (F:(i->i),(λ#1:i.g(#3(#1:i):i, #5(#1:i):i):i))
  // 4 b
  def transformation4b(uprobl : List[Pair[HOLExpression, HOLExpression]])(implicit disAllowedVars: Set[Var] ) :  List[ConfigurationNode] = {
    uprobl match {
        case (AbsN(varList1, AppN(funcVar: HOLVar, args1)), AbsN(varList2, AppN(funcVar2: HOLConst, args2)))::s => {
         val dv  = disAllowedVars.foldLeft(scala.collection.immutable.Set[Var]())((ls,x) => ls.+(x))
//         println("\nrule (4'b)\n")
         val newVarList = args1.map(x => {val fv = freshVar.apply1(x.exptype, dv, funcVar).asInstanceOf[HOLVar]; disAllowedVars+=fv; fv.asInstanceOf[HOLVar]} )
//         println("\nnewVarList.size  =  "+newVarList.size)
         val generalFlexibleTermListOfList: List[List[HOLVar]] = newVarList.map(x => {
           x.exptype match {
             case Ti() => List[HOLVar]()

             case FunctionType(to, lsArgs ) => {
               lsArgs.map(x1 => HuetAlgorithm.createFuncVarH(newVarList.asInstanceOf[List[HOLVar]], HuetAlgorithm.getListOfZs(x1)).asInstanceOf[HOLVar])
             }
           }
         })

//         println("\n generalFlexibleTermListOfList =  ")
//         generalFlexibleTermListOfList.map(x => { x.map(y => {println(y.toString+"  ; ");y});   println("  \n ");x})

//         println("\n 2 \n")
         val listOfArgsOfY_i = generalFlexibleTermListOfList.zip(newVarList).map(x => {
           x._1 match {
             case Nil => List[HOLVar]()
             case _ => {
               x._2.exptype match {
                 case FunctionType(to, lsArgs ) =>  (x._1.zip(lsArgs)).map(y => {val zs = HuetAlgorithm.getListOfZs(y._2) ;val h = AbsN(zs, AppN(AppN(y._1, newVarList), zs)); println("\nh = "+h.toString1+"  :  "+h.exptype.toString ); h})
                 case Ti() => {println("\nERROR in 2\n"); List[HOLVar]()}
                 }
             }
           }
         })
//         println("\n listOfArgsOfY_i =  ")
//         listOfArgsOfY_i.map(x => { x.map(y => {println(y.toString1+"  ; ");y});   println("  \n ");x})

//         println("\n 3 \n")
         val listOfY_i = (newVarList.zip(listOfArgsOfY_i)).map(x => {
           x._2 match {
             case List() => x._1
             case _   => {println("\nx._1.exptype = "+x._1.exptype); println("\nx._2 list = "+x._2.head.exptype.toString); AppN(x._1,x._2)}
           }
         })


//         println("\n 4 \n")

         val listOfPartBindings = (newVarList.zip(listOfY_i)).map(x => {
           x._2 match {
             case List() => AbsN(newVarList, x._1).asInstanceOf[HOLExpression]
             case _ => AbsN(newVarList, x._2).asInstanceOf[HOLExpression]
           }
         })

//         println("\n 5 \n")

         val listOfSubstPartBindPair = (listOfPartBindings.map(x => Substitution[HOLExpression](funcVar, x))).zip(listOfPartBindings)

         val llist = listOfSubstPartBindPair.map(x => Tuple2(HuetAlgorithm.applySubToListOfPairs(s,x._1), x._2))
         val newl = llist.map(x => {
            val sigma = Substitution[HOLExpression](funcVar, x._2);
//            new ConfigurationNode(HuetAlgorithm.applySubToListOfPairs( uprobl.tail, sigma), Pair(funcVar, x._2)::HuetAlgorithm.applySubToListOfPairs( subList, sigma))
            new ConfigurationNode(HuetAlgorithm.applySubToListOfPairs( uprobl, sigma), Pair(funcVar, x._2)::HuetAlgorithm.applySubToListOfPairs( subList, sigma))
//            println("L:+  "+(l:+(new ConfigurationNode(Pair(HuetAlgorithm.applySubToListOfPairs( conf.currentConf._1.tail, sigma), Pair(funcVar, x._2)::HuetAlgorithm.applySubToListOfPairs( conf.currentConf._2, sigma))))).toString)
           })
//          println("\nnewl = "+newl.toString)
         return newl



//         println("\n(4'b) end : "+listOfSubstPartBindPair.toString+"\n")
//         println("\nrule 4b,  l:+  = "+l.toString)
  //       unifySetOfTuples(rest:::l)

    //            println("\n(4'b) end :\n"+(rest:::((Tuple2(applySubToListOfPairs(s,sigma), (funcVar,part_bind_t)::s2))::Nil)).toString+"\n")
    //
    //            unifySetOfTuples(rest:::((Tuple2(applySubToListOfPairs(s,sigma), (funcVar,part_bind_t)::s2))::Nil))
        }
      }
  }

}




//class ConfigurationNode(val currentConf: Pair[List[Pair[HOLExpression, HOLExpression]], List[Pair[HOLExpression, HOLExpression]]]) extends Configuration[Substitution[HOLExpression]] {
//
//  override def toString = "( "+currentConf._1.toString+" ; "+currentConf._2.toString+" )"
//
//
//  def isTerminal: Boolean = currentConf._1 match {
//    case List() => true
//    case _ => false
//  }
//
//  def result: Option[Substitution[HOLExpression]] = currentConf._1 match {
//    case List() => Some(Substitution[HOLExpression](currentConf._2.map( x => (x._1.asInstanceOf[HOLVar],x._2) )))
//    case _ => None
//  }
//
//  def isRule1Applicable : Boolean = currentConf._1 match {
//    case (t1,t2)::s if t1 == t2 => true
//    case _ => false
//  }
//
//  def isRule2Applicable : Boolean = currentConf._1 match {
//    case ((AbsN(varList1, Function(sym1 : ConstantStringSymbol, args1, returnType1)),AbsN(varList2, Function(sym2 : ConstantStringSymbol, args2, returnType2)))::s)
//      if sym1 == sym2 && varList1.size == varList2.size && returnType1 == returnType2 => true
//    case _ => false
//  }
//
//  def isRule3Applicable : Boolean = currentConf._1 match {
//    case (AbsN(varList1, AppN(funcVar: HOLVar, args1)), AbsN(varList2, exp))::s if varList1.size == varList2.size && exp.exptype == funcVar.exptype => true
//    case (AbsN(varList2, exp), AbsN(varList1, AppN(funcVar: HOLVar, args1)))::s if varList1.size == varList2.size && exp.exptype == funcVar.exptype => true
//    case _ => false
//  }
//
//  def isRule4aApplicable : Boolean = currentConf._1 match {
//    case (AbsN(varList1, AppN(funcVar: HOLVar, args1)), AbsN(varList2, Function(sym : ConstantStringSymbol, args2, returnType)))::s if varList1==varList2 => true
//    case (AbsN(varList2, Function(sym : ConstantStringSymbol, args2, returnType)), AbsN(varList1, AppN(funcVar: HOLVar, args1)))::s if varList1==varList2 => true
//    case _ => false
//  }
//
//  def isRule4bApplicable : Boolean = currentConf._1 match {
//    case (AbsN(varList1, AppN(funcVar: HOLVar, args1)), AbsN(varList2, AppN(funcVar2: HOLConst, args2)))::s if varList1==varList2 => true
//    case (AbsN(varList2, AppN(funcVar2: HOLConst, args2)), AbsN(varList1, AppN(funcVar: HOLVar, args1)))::s if varList1==varList2 => true
//    case _ => false
//  }
//}




object HuetAlgorithm extends UnificationAlgorithm[HOLExpression]
{

//    class MyConfirguration extends Configuration[Substitution[HOLExpression]]{
//      def isTerminal = result != None
//    }

    def myFun1(conf1: Configuration[Substitution[HOLExpression]])(implicit disAllowedVars: Set[Var] ): List[Configuration[Substitution[HOLExpression]]] = {
      val conf = conf1.asInstanceOf[ConfigurationNode]
      val uproblems = conf.uproblems
//      println("\n\ncurrent configuration = " + conf1.toString+ "\n\n")
      println("\n\nunification problems list: \n\n"+uproblems.map(x => Pair(x._1.toStringSimple, x._2.toStringSimple))+"\n")
      uproblems match {
        case (t1,t2)::s if t1 == t2 => conf.transformation1::Nil // (1)
        case (AbsN(varList1, Function(sym1 : ConstantStringSymbol, args1, returnType1)),AbsN(varList2, Function(sym2 : ConstantStringSymbol, args2, returnType2)))::s
          if sym1 == sym2 && varList1.size == varList2.size && returnType1 == returnType2 => conf.transformation2::Nil //2

        case (AbsN(varList1, AppN(funcVar: HOLVar, args1)), AbsN(varList2, Function(sym : ConstantStringSymbol, args2, returnType)))::s if varList1==varList2 =>{
//          println("\nmyFyn case 4ab => \n");
//          println("\nREZ : "+(conf.transformation4a(uproblems) :: conf.transformation4b(uproblems)).toString)
          val cl = conf.transformation4a(uproblems) :: conf.transformation4b(uproblems)
//          cl.foreach(co => println("\nco = "+co.toString))
          cl
        }

        case (AbsN(varList2, Function(sym : ConstantStringSymbol, args2, returnType)), AbsN(varList1, AppN(funcVar: HOLVar, args1)))::s if varList1==varList2 => {
//          println("\nmyFyn case 4ab1 => \n");
          val cl = conf.transformation4a(Pair(AbsN(varList1, AppN(funcVar, args1)), AbsN(varList2, Function(sym, args2.asInstanceOf[List[HOLExpression]], returnType))).asInstanceOf[Pair[HOLExpression,HOLExpression]] :: uproblems.tail) :: conf.transformation4b(Pair(AbsN(varList1, AppN(funcVar, args1)), AbsN(varList2, Function(sym, args2.asInstanceOf[List[HOLExpression]], returnType))).asInstanceOf[Pair[HOLExpression,HOLExpression]] :: uproblems.tail)
//          cl.foreach(co => println("\nco = "+co.toString))
          cl
        }
//        case (AppN(funcVar: HOLVar, args1), Function(sym : ConstantStringSymbol, args2, returnType))::s  => {
        case (AppN(funcVar: HOLVar, args1), AppN(funcVar2: HOLConst, args2))::s  => {
//          println("\nmyFyn case 4ab2 => \n");
          val cl = conf.transformation4a(Pair(AppN(funcVar, args1), AppN(funcVar2: HOLConst, args2)).asInstanceOf[Pair[HOLExpression,HOLExpression]] :: uproblems.tail) :: conf.transformation4b(Pair(AppN(funcVar, args1), AppN(funcVar2: HOLConst, args2)).asInstanceOf[Pair[HOLExpression,HOLExpression]] :: uproblems.tail)
//          cl.foreach(co => println("\nco = "+co.toString))
          cl
        }

        case _ => {
          println("\nNo unifier! ")
//          println("\nmyFyn unapply : "+uproblems.head._1+"            "+HOLVar.unapply(uproblems.head._1).get)
//          conf1.isTerminal = true


//          List[Configuration[Substitution[HOLExpression]]]()
          conf1::List[Configuration[Substitution[HOLExpression]]]()
        }
      }
    }



    def unify1(t1: HOLExpression, t2: HOLExpression) : NDStream[Substitution[HOLExpression]] with BFSAlgorithm = {
      implicit val disAllowedVars = Set[Var]()
      val st = new NDStream(new ConfigurationNode((t1,t2)::Nil , Nil), myFun1) with BFSAlgorithm
//      st.init
      return st
    }
    def unify(term1: HOLExpression, term2: HOLExpression) : List[Substitution[HOLExpression]] = List()
//    def unify(term1: HOLExpression, term2: HOLExpression) : List[Substitution[HOLExpression]] =
//    {
//      implicit val disAllowedVars = Set[Var]()
//      unifySetOfTuples(Tuple2((Tuple2(term1.asInstanceOf[HOLExpression],term2.asInstanceOf[HOLExpression]))::Nil, Nil)::Nil) match
//      {
//        case Some((Nil,ls)::_) => List(Substitution[HOLExpression](ls.map(x => (x._1.asInstanceOf[HOLVar],x._2))))
//        case _ => Nil
//      }
//    }

    def applySubToListOfPairs(l : List[Tuple2[HOLExpression, HOLExpression]], s : Substitution[HOLExpression]) : List[Tuple2[HOLExpression, HOLExpression]] =
    {
    //  l.foldLeft(Nil)((Tuple2(x,v))=> (Tuple2(s.applyFOL(x),s.applyFOL(v))))
//      return l.map(a => (BetaReduction.betaNormalize(s.apply(a._1))(Outermost).asInstanceOf[HOLExpression], s.apply(a._2)))
        return l.map(a => (BetaReduction.betaNormalize(s.apply(a._1))(Outermost).asInstanceOf[HOLExpression], BetaReduction.betaNormalize(s.apply(a._2))(Outermost).asInstanceOf[HOLExpression]))
    }









  //  def unifySetOfTuples(s1: List[Tuple2[HOLExpression, HOLExpression]], s2 : List[Tuple2[HOLExpression,HOLExpression]]) : Option[(List[Tuple2[HOLExpression,HOLExpression]], List[Tuple2[HOLExpression,HOLExpression]])] = (s1,s2) match
    def unifySetOfTuples(queue: List[Tuple2[List[Tuple2[HOLExpression, HOLExpression]], List[Tuple2[HOLExpression,HOLExpression]]]])(implicit disAllowedVars: Set[Var] ) : Option[List[Tuple2[List[Tuple2[HOLExpression, HOLExpression]], List[Tuple2[HOLExpression,HOLExpression]]]]] = queue match
    {

      case (Nil, s2)::rest => { println("\nSubstitution found : \n"+s2); Some((Nil,s2)::Nil)  }

      case (s1,s2)::rest => (s1,s2) match

      {
        //rule (1)
        case (((a1,a2)::s), s2) if a1 == a2 =>
              {
                println("\nrule (1)\n")
                unifySetOfTuples(Tuple2(s, s2)::rest)
              }

        //rule (2')
        case ((AbsN(varList1, Function(sym1 : ConstantStringSymbol, args1, returnType1)),AbsN(varList2, Function(sym2 : ConstantStringSymbol, args2, returnType2)))::s, s2)
          if sym1 == sym2 && varList1.size == varList2.size && returnType1 == returnType2 =>
          {
            println("\nrule (2)\n")
            val l = args1.map(x => AbsN(varList1,x)).zip(args2.map(x => AbsN(varList2,x))):::s
            unifySetOfTuples(rest:::(Tuple2(l.asInstanceOf[List[Tuple2[HOLExpression, HOLExpression]]],s2.asInstanceOf[List[Tuple2[HOLExpression, HOLExpression]]])::Nil))
          }



        //rule (3)
        case ((AbsN(varList1, AppN(funcVar: HOLVar, args1)), v @ AbsN(varList2, exp))::s, s2)
          if varList1.size == varList2.size && exp.exptype == funcVar.exptype =>
          {
            println("\nrule (3)\n")
            val sigma = Substitution[HOLExpression](funcVar, v)
            unifySetOfTuples(rest:::(Tuple2((funcVar,v)::applySubToListOfPairs(s,sigma), (funcVar,v)::s2)::Nil))
          }




        //rule (4'a)
        case ((AbsN(varList1, AppN(funcVar: HOLVar, args1)), AbsN(varList2, Function(sym : ConstantStringSymbol, args2, returnType)))::s, s2)
          if varList1==varList2 =>
          {
//            println("\nrule (4'a)\n")
            val dv  = disAllowedVars.foldLeft(scala.collection.immutable.Set[Var]())((ls,x) => ls.+(x))
//                println("\n\n"+disAllowedVars.toString)
//                val fv = freshVar(z, dv, x); disAllowedVars += fv; fv
            val newVarList = args1.map(x => {val fv = freshVar.apply1(x.exptype, dv, funcVar); disAllowedVars+=fv; fv} )
//            println("\n222    disAllowedVars : +"+disAllowedVars.toString+"\n")
//            println("\n222    newVarList : +"+newVarList.toString+"\n")
            val generalFlexibleTermList = args2.map(x1 => createFuncVarH(newVarList.asInstanceOf[List[HOLVar]], getListOfZs(x1.exptype)))
//            println("\n333  newVarList : " +newVarList.toString+      "          generalFlexibleTermList : "+generalFlexibleTermList.toString+" \n")

            val zHlist = generalFlexibleTermList.zip(args2.map(x => getListOfZs(x.exptype))).map(x => AbsN(x._2, x._1))
//            println("\n444\n"+zHlist.toString)


            val appzHlist = zHlist.map(x => {
//              EtaExpand.s = (EtaExpand.s).union(disAllowedVars);
//              val dum = EtaExpand.apply( AppN(x, newVarList))

              val ev = EtaExpand.apply( AppN(x, newVarList));
              disAllowedVars.union(ev.getFreeAndBoundVariables._1);
              disAllowedVars.union(ev.getFreeAndBoundVariables._2);
//              println("\n4444555   "+ disAllowedVars.toString +"\n")
              ev
            })


            val term = AppN(Var(sym, returnType,funcVar.factory), appzHlist)
//            println("\n555   "  + term.toString1+ " \n")
            val part_bind_t = AbsN(newVarList, term ).asInstanceOf[HOLExpression]
//            println("\n666 binding = "+ part_bind_t.toString1 +" \n")

            val sigma = Substitution[HOLExpression](funcVar, part_bind_t)

            println("\n(4'a) end :\n"+(rest:::((Tuple2(applySubToListOfPairs(s,sigma), (funcVar,part_bind_t)::s2))::Nil)).toString+"\n")

            unifySetOfTuples(rest:::((Tuple2(applySubToListOfPairs(s,sigma), (funcVar,part_bind_t)::s2))::Nil))
//            Some(rest:::(Tuple2((funcVar,part_bind_t)::s1 ,s2)::Nil))
          }



        //rule (4'b)
        case ((AbsN(varList1, AppN(funcVar: HOLVar, args1)), AbsN(varList2, AppN(funcVar2: HOLConst, args2)))::s, s2)
          if varList1==varList2 => //&& varList2.contains(funcVar2)=>
          {
            val dv  = disAllowedVars.foldLeft(scala.collection.immutable.Set[Var]())((ls,x) => ls.+(x))
//            println("\nrule (4'b)\n")
            val newVarList = args1.map(x => {val fv = freshVar.apply1(x.exptype, dv, funcVar).asInstanceOf[HOLVar]; disAllowedVars+=fv; fv.asInstanceOf[HOLVar]} )
//            println("\nnewVarList.size  =  "+newVarList.size)
            val generalFlexibleTermListOfList: List[List[HOLVar]] = newVarList.map(x => {
              x.exptype match {
                case Ti() => List[HOLVar]()

                case FunctionType(to, lsArgs ) => {
                  lsArgs.map(x1 => createFuncVarH(newVarList.asInstanceOf[List[HOLVar]], getListOfZs(x1)).asInstanceOf[HOLVar])
                }
              }
            })

//            println("\n generalFlexibleTermListOfList =  ")
            generalFlexibleTermListOfList.map(x => { x.map(y => {println(y.toString+"  ; ");y});   println("  \n ");x})

//            println("\n 2 \n")
            val listOfArgsOfY_i = generalFlexibleTermListOfList.zip(newVarList).map(x => {
              x._1 match {
                case Nil => List[HOLVar]()
                case _ => {
                  x._2.exptype match {
                    case FunctionType(to, lsArgs ) =>  (x._1.zip(lsArgs)).map(y => {val zs = getListOfZs(y._2) ;val h = AbsN(zs, AppN(AppN(y._1, newVarList), zs)); println("\nh = "+h.toString1+"  :  "+h.exptype.toString ); h})
                    case Ti() => {println("\nERROR in 2\n"); List[HOLVar]()}
                    }
                }
              }
            })
//            println("\n listOfArgsOfY_i =  ")
//            listOfArgsOfY_i.map(x => { x.map(y => {println(y.toString1+"  ; ");y});   println("  \n ");x})

//            println("\n 3 \n")
            val listOfY_i = (newVarList.zip(listOfArgsOfY_i)).map(x => {
              x._2 match {
                case List() => x._1
                case _   => {println("\nx._1.exptype = "+x._1.exptype); println("\nx._2 list = "+x._2.head.exptype.toString); AppN(x._1,x._2)}
              }
            })


//             println("\n 4 \n")

            val listOfPartBindings = (newVarList.zip(listOfY_i)).map(x => {
              x._2 match {
                case List() => AbsN(newVarList, x._1).asInstanceOf[HOLExpression]
                case _ => AbsN(newVarList, x._2).asInstanceOf[HOLExpression]
              }
            })

//            println("\n 5 \n")

            val listOfSubstPartBindPair = (listOfPartBindings.map(x => Substitution[HOLExpression](funcVar, x))).zip(listOfPartBindings)

            val l = listOfSubstPartBindPair.map(x => Tuple2(applySubToListOfPairs(s,x._1), (funcVar,x._2)::s2))

//            println("\n(4'b) end :\n"+(rest:::((Tuple2(applySubToListOfPairs(s,sigma), (funcVar,part_bind_t)::s2))::Nil)).toString+"\n")

            unifySetOfTuples(rest:::l)

//            println("\n(4'b) end :\n"+(rest:::((Tuple2(applySubToListOfPairs(s,sigma), (funcVar,part_bind_t)::s2))::Nil)).toString+"\n")
//
//            unifySetOfTuples(rest:::((Tuple2(applySubToListOfPairs(s,sigma), (funcVar,part_bind_t)::s2))::Nil))
          }




        case (( App(var1,exp1) , App(var2,exp2))::s, s2) =>
          {
            val y = HOLVar(new VariableStringSymbol("y"), Ti())
            println("\n\n!!!\n\n")
            unifySetOfTuples((Tuple2(Abs(y, App(var1,exp1)).asInstanceOf[HOLExpression], Abs(y,App(var2,exp2)).asInstanceOf[HOLExpression])::s ,s2)::rest)
        //    println("\n\n!!!\n\n")
//            (None)
          }

        case _ => { println("\nNothing !!!\n"); (None)  }

      }

      case Nil => { println("\nNo match !!!\n"); (None)  }
    }

  //gives the list of z_1^i,...,z_{p_i}^i
  def getListOfZs(exptype: TA)(implicit disAllowedVars: Set[Var] ) : List[HOLVar] =
  {
//    println("\n getListOfZs \n")
    val k = HOLVar(VariableStringSymbol("x"), Ti())
    val l1 = List[HOLVar]()
    exptype match {
      case Ti() => {
//                     println("\n getListOfZs 1\n")
                     val dv  = disAllowedVars.foldLeft(scala.collection.immutable.Set[Var]())((ls,x) => ls.+(x))
                     val fv = freshVar.apply1(exptype ,dv, k ).asInstanceOf[HOLVar]
                     disAllowedVars.+(fv);
                     disAllowedVars.union(fv.getFreeAndBoundVariables._1)
                     disAllowedVars.union(fv.getFreeAndBoundVariables._2)
//        println("\n"+fv.toString+"\n")
//                     return fv::Nil
                      return l1
      }
      case FunctionType(to, lsArgs ) => {
//        println("\n getListOfZs 2\n")
        val ls:List[HOLVar] = lsArgs.map(z => {
          val dv  = disAllowedVars.foldLeft(scala.collection.immutable.Set[Var]())((ls,x) => ls.+(x))
          val fv = freshVar.apply1(z, dv, k); disAllowedVars.+(fv);
          disAllowedVars.union(fv.getFreeAndBoundVariables._1)
          disAllowedVars.union(fv.getFreeAndBoundVariables._2)
          fv.asInstanceOf[HOLVar]
        })
//        println("\n getListOfZs END\n")
//        println("\n"+ls.toString+"\n")
        ls
      }
      case _ => { println("\n ERROR in getListOfZs \n"); l1}
    }
  }

  //gives a H_i
  def createFuncVarH(ys: List[HOLVar], ls: List[HOLVar])(implicit disAllowedVars: Set[Var] ) : Var =
  {
//    println("\ncreateFuncVarH       disAllowedVars : "+disAllowedVars.toString+"\n")
//    println("\nys:::ls = "+ ys.toString+" ::: "+ls.toString +"\n")
    val k: HOLVar = HOLVar(VariableStringSymbol("x"), Ti()).asInstanceOf[HOLVar]
//    println("\ncreateFuncVarH 1   "+ FunctionType(Ti(), ys.map(x => x.exptype)) +"\n")
    val dv  = disAllowedVars.foldLeft(scala.collection.immutable.Set[Var]())((ls,x) => ls.+(x))
    val fv: Var = freshVar.apply1(FunctionType.apply(Ti(), (ys:::ls).map(x => x.exptype)), dv, k)
    disAllowedVars.union(fv.getFreeAndBoundVariables._1)
    disAllowedVars.union(fv.getFreeAndBoundVariables._2)
//    println("\nfv = "+ fv.toString +"\n")
    disAllowedVars.+(fv)
//    println("\ncreateFuncVarH end          fv = "+fv.toString+"\n")
    fv
  }

}









