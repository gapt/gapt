package algorithms.unification.hol

/**
 * Created by IntelliJ IDEA.
 * User: cdunchev
 * Date: 5/19/11
 * Time: 11:16 AM
 * To change this template use File | Settings | File Templates.
 */

package huet {


import at.logic.algorithms.unification.hol._

import scala.collection.immutable.{Map, HashMap}
import at.logic.utils.executionModels.searchAlgorithms.BFSAlgorithm
import at.logic.language.lambda.types. {->, Ti, TA, FunctionType}
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.algorithms.unification.UnificationAlgorithm
import at.logic.language.hol._
import at.logic.language.hol.HOLExpression

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

  private[huet] class MyConfiguration(val uproblems: List[Tuple2[HOLExpression,HOLExpression]], val result: Option[Substitution[HOLExpression]], val isTerminal: Boolean) extends Configuration[Substitution[HOLExpression]] {
        def this() = this(List(), None, true) // for failure
        def this(result: Option[Substitution[HOLExpression]]) = this(List(), result, true) // for success
        def this(l: List[Tuple2[HOLExpression,HOLExpression]]) = this(l, None, false) // for in node
        def toStr  = uproblems.map(x => ("<"+x._1.toStringSimple+", "+ x._2.toStringSimple+">"))}

  object Huet {
    def apply(uproblems: List[Tuple2[HOLExpression,HOLExpression]]): NDStream[Substitution[HOLExpression]] =
      if (!validateTypes(uproblems))
        throw new IllegalArgumentException("Types of pairs do not match")
      else {
//        implicit val disAllowedVars = Set[Var]()
        new NDStream[Substitution[HOLExpression]](new MyConfiguration(uproblems, None, false), MyFun) with BFSAlgorithm
      }

    def apply(e1 : HOLExpression, e2 : HOLExpression): NDStream[Substitution[HOLExpression]] = apply((e1,e2)::Nil)




    private[huet] object MyFun extends Function1[Configuration[Substitution[HOLExpression]], List[Configuration[Substitution[HOLExpression]]]] {
//      def apply(conf2: Configuration[Substitution[HOLExpression]]) = {println("wrong apply"); apply(conf2,Set[Var]() )}

      def apply(conf2: Configuration[Substitution[HOLExpression]]): List[Configuration[Substitution[HOLExpression]]] = {
        implicit val disAllowedVars: Set[Var] = Set[Var]()
        val conf = conf2.asInstanceOf[MyConfiguration]
        println("\n\nconf = "+conf.toStr)
        if (inPreSolvedForm(conf.uproblems)) {
          println("terminal+result")
          (new MyConfiguration(Some(createSub(conf.uproblems))))::Nil
        }
        else conf.uproblems match {

          case (v,u)::uptail if u == v => List(new MyConfiguration(uptail))  // (1)

          case (HOLVar(n1,t1), HOLVar(n2,t2))::uptail => List(new MyConfiguration(pushPreSolvedToEnd(conf.uproblems)))

          case (AbsN(_,AppN1(v,ls1)),AbsN(_,AppN1(u,ls2)))::uptail if v == u => (new MyConfiguration( (ls1.zip(ls2).asInstanceOf[List[Tuple2[HOLExpression,HOLExpression]]]) ::: uptail))::Nil  // (2)

          // (3)
          case (AbsN(args1,AppN(f,ls1)), v @ AbsN(args2,_))::uptail if etaSimplifiedForm(args1.asInstanceOf[List[HOLExpression]], ls1.asInstanceOf[List[HOLExpression]])
               && notInFreeVarsOf(f.asInstanceOf[HOLExpression],v)
               && isHOLVar(f.asInstanceOf[HOLExpression])
               && args1.size == args2.size => {
              val sub = createSub(Pair(f, v).asInstanceOf[Pair[HOLExpression, HOLExpression]]::Nil)
              val newConf = (new MyConfiguration(pushPreSolvedToEnd((f.asInstanceOf[HOLExpression],v)::betaNormalize(applySubToListOfPairs(sub,uptail)))))
              newConf::Nil
          }

          case (v @ AbsN(args2,_), AbsN(args1,AppN(f,ls1)))::uptail if etaSimplifiedForm(args1.asInstanceOf[List[HOLExpression]], ls1.asInstanceOf[List[HOLExpression]])
               && notInFreeVarsOf(f.asInstanceOf[HOLExpression],v)
               && isHOLVar(f.asInstanceOf[HOLExpression])
               && args1.size == args2.size => {
              val sub = createSub(Pair(f, v).asInstanceOf[Pair[HOLExpression, HOLExpression]]::Nil)
              val newConf = (new MyConfiguration(pushPreSolvedToEnd((f.asInstanceOf[HOLExpression],v)::betaNormalize(applySubToListOfPairs(sub,uptail)))))
              newConf::Nil
          }
//
//

          //4a
          case (t1 @ AbsN(args1,AppN1(f,ls1)), t2 @ AbsN(args2,AppN1(a,ls2)))::rest if isHOLVar(f.asInstanceOf[HOLExpression]) && (isFreeVarIn(a.asInstanceOf[HOLExpression], t2) || isFunctionConstantSymbol(a.asInstanceOf[HOLExpression]) )=> // (4)
              {
                println("imitation 4a")
//                val t = partialBindingImitation(a.asInstanceOf[HOLVar],f.asInstanceOf[HOLVar])
//                val t = pairPartialBindingImitation((t1, t2)::rest)._1
//                (new MyConfiguration(pushPreSolvedToEnd((t1, t2)::rest))) ::Nil  // (4a)
                val imitation = pairPartialBindingImitation((t1, t2)::rest)._2
//                pairPartialBindingImitation((t1, t2)::rest)._2

//               :::// Nil
//              (
//                if (isFunctionConstantSymbol(a.asInstanceOf[HOLExpression]) || args2.contains(a)) args1.map(x => {
//                  val t = partialBindingProjection((t1, t2)::rest)
//                  new MyConfiguration(pushPreSolvedToEnd((f.asInstanceOf[HOLExpression],t)::conf.uproblems))  // (4b)
//                })
//                else List()
//              )
              (
                if (isFunctionConstantSymbol(a.asInstanceOf[HOLExpression]) || args2.contains(a))
                  imitation ::: listOfProjections((t1, t2)::rest)
                else
                  imitation ::: List()
              )}
         case _ => List()
       }
      }
    }

    private[huet] def validateTypes(ls: List[Tuple2[HOLExpression,HOLExpression]]): Boolean = ls match {
      case x::rest => x._1.exptype == x._2.exptype && validateTypes(rest)
      case _ => true
    }


    private[huet] def inPreSolvedForm(ls: List[Tuple2[HOLExpression,HOLExpression]]): Boolean = ls match {
      case head::rest => {
        head match {
          case (HOLVar(n1,t1), HOLVar(n2,t2)) => inPreSolvedForm(rest)
          case (v @ HOLVar(n1,t1), e: HOLExpression)   => {
            if (e.getFreeAndBoundVariables._1.contains(v.asInstanceOf[Var]) || e.getFreeAndBoundVariables._2.contains(v.asInstanceOf[Var]))
              return false
            rest.foreach(x =>
              if (x._1.getFreeAndBoundVariables._1.contains(v.asInstanceOf[Var]) || x._1.getFreeAndBoundVariables._2.contains(v.asInstanceOf[Var]) || x._2.getFreeAndBoundVariables._1.contains(v.asInstanceOf[Var]) || x._2.getFreeAndBoundVariables._2.contains(v.asInstanceOf[Var]))
                return false
                        )
            inPreSolvedForm(ls.tail)
          }
          case (e: HOLExpression, v @ HOLVar(n1,t1))  =>{
            if (e.getFreeAndBoundVariables._1.contains(v.asInstanceOf[Var]) || e.getFreeAndBoundVariables._2.contains(v.asInstanceOf[Var]))
              return false
            rest.foreach(x =>
              if (x._1.getFreeAndBoundVariables._1.contains(v.asInstanceOf[Var]) || x._1.getFreeAndBoundVariables._2.contains(v.asInstanceOf[Var]) || x._2.getFreeAndBoundVariables._1.contains(v.asInstanceOf[Var]) || x._2.getFreeAndBoundVariables._2.contains(v.asInstanceOf[Var]))
                return false
                        )
            inPreSolvedForm(ls.tail)
          }
          case _ => {
            println("inPreSolvedForm == false")
            false
          }
        }
      }
      case List() => true
      case _ => false
    }

    private[huet] def pushPreSolvedToEnd(l: List[Tuple2[HOLExpression,HOLExpression]]): List[Tuple2[HOLExpression,HOLExpression]] = l match {
      case x::rest => rest:::(x::Nil)
      case _ => l
    }

    private[huet] def etaSimplifiedForm(ls: List[HOLExpression],ls2: List[HOLExpression]): Boolean = {
      true

    }
    private[huet] def notInFreeVarsOf(v: HOLExpression, u: HOLExpression): Boolean = !u.getFreeAndBoundVariables._1.contains(v.asInstanceOf[Var])


    private[huet] def createSub(ls: List[Tuple2[HOLExpression,HOLExpression]]): Substitution[HOLExpression] = {
      val map: Map[Var, HOLExpression] = new HashMap[Var, HOLExpression]()
      val new_map = ls.foldLeft(map)((x,y)=> {
        y._1 match {
          case HOLVar(n,t) => x + ((y._1.asInstanceOf[Var], y._2.asInstanceOf[HOLExpression]))
          case _ => x + ((y._2.asInstanceOf[Var], y._1.asInstanceOf[HOLExpression]))
        }
      })
      new Substitution(new_map)
    }


    private[huet] def applySubToListOfPairs(s : Substitution[HOLExpression], l : List[Tuple2[HOLExpression, HOLExpression]]) : List[Tuple2[HOLExpression, HOLExpression]] = {
        return l.map(a => (BetaReduction.betaNormalize(s.apply(a._1))(Outermost).asInstanceOf[HOLExpression], BetaReduction.betaNormalize(s.apply(a._2))(Outermost).asInstanceOf[HOLExpression]))
    }


    private[huet] def betaNormalize(exp: List[Pair[HOLExpression,HOLExpression]]): List[Pair[HOLExpression,HOLExpression]] = {
      exp.map(x => (BetaReduction.betaNormalize(x._1 )(Outermost).asInstanceOf[HOLExpression], BetaReduction.betaNormalize(x._2 )(Outermost).asInstanceOf[HOLExpression]))
    }
    private[huet] def isFreeVar(v: HOLVar): Boolean  = false



//    private[huet] def partialBindingImitation(a:HOLVar, F:HOLVar): HOLExpression = a
//    private[huet] def partialBindingProjection(a:HOLVar, F:HOLVar): HOLExpression = a



    def isFreeVarIn(v : HOLExpression, t1: HOLExpression): Boolean = {
//      println("isFreeVarIn = ")
//      println(!t1.getFreeAndBoundVariables._2.contains(v.asInstanceOf[Var]))
      !t1.getFreeAndBoundVariables._2.contains(v.asInstanceOf[Var])
    }

    def isFunctionConstantSymbol(v: HOLExpression): Boolean ={
      println("isFunctionConstantSymbol")
      v match {
        case HOLConst(n,t) => true
        case _ => false
      }
    }

    def isHOLVar(f: HOLExpression): Boolean = f match {
      case HOLVar(n,t) => true
      case _ => false
    }



    def pairPartialBindingImitation(uprobl : List[Pair[HOLExpression, HOLExpression]])(implicit disAllowedVars: Set[Var] ) :  Tuple2[HOLExpression, List[Configuration[Substitution[HOLExpression]]]] = {
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



//            val newConfNode = new ConfigurationNode((HuetAlgorithm.applySubToListOfPairs(uprobl, sigma)).map(x => (x._1, BetaReduction.betaNormalize(x._2 )(Outermost)).asInstanceOf[Pair[HOLExpression, HOLExpression]]) ,
//              (funcVar,part_bind_t)::HuetAlgorithm.applySubToListOfPairs(uprobl.tail,sigma))

            val newConfNode = (new MyConfiguration((HuetAlgorithm.applySubToListOfPairs(uprobl.tail, sigma)).map(x => (x._1, BetaReduction.betaNormalize(x._2 )(Outermost)).asInstanceOf[Pair[HOLExpression, HOLExpression]]) :::((funcVar,part_bind_t) ::Nil), None, false))

//            println("\nl:+  "+(new ConfigurationNode(Tuple2(HuetAlgorithm.applySubToListOfPairs(conf.currentConf._1.tail,sigma), (funcVar,part_bind_t)::HuetAlgorithm.applySubToListOfPairs(conf.currentConf._2,sigma))))).toString()
//            println("\n 4a, newConfNode = "+newConfNode.toString)
            println("imitation newConfNode = "+newConfNode.toStr)

            Pair(part_bind_t, newConfNode::Nil)
//            println("\nrule 4a,  l:+ = "+l.toString)
          }
          case _ => println("\nError in 4a\n") ; exit(0)
        }
    }


  def listOfProjections(uprobl : List[Pair[HOLExpression, HOLExpression]])(implicit disAllowedVars: Set[Var] ) :  List[Configuration[Substitution[HOLExpression]]] = {
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
//            new ConfigurationNode(HuetAlgorithm.applySubToListOfPairs( uprobl, sigma), Pair(funcVar, x._2)::HuetAlgorithm.applySubToListOfPairs( subList, sigma))

           new MyConfiguration(HuetAlgorithm.applySubToListOfPairs( uprobl.tail, sigma) :::( Pair(funcVar, x._2)::Nil))
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
      case _ =>  println("\nError in 4b\n");exit(1)
      }
  }

  }
}
