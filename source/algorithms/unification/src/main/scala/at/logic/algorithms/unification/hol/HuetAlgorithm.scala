/*
Fixing this seems to require a better understanding of the algorithm due to the
extensive use of AppN (which no longer exists). Since it is not being used anywhere, I am commenting
it out for now. [Giselle]

package at.logic.algorithms.unification.hol

package huet {

import at.logic.language.lambda.etaExpansion._
import scala.collection.immutable.HashMap
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
import scala.collection.mutable.{Set => MSet}
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
        def toStr  = uproblems.map(x => ("<"+x._1.toStringSimple+", "+ x._2.toStringSimple+">"))
  }



  object Huet {

    def apply(uproblems: List[Tuple2[HOLExpression,HOLExpression]]): NDStream[Substitution[HOLExpression]] =
      if (!validateTypes(uproblems))
        throw new IllegalArgumentException("Types of pairs do not match")
      else {
        new NDStream[Substitution[HOLExpression]](new MyConfiguration(etaBetaNormalization(uproblems), None, false), MyFun) with BFSAlgorithm
      }

    def apply(e1 : HOLExpression, e2 : HOLExpression): NDStream[Substitution[HOLExpression]] = apply((e1,e2)::Nil)



    private[huet] object MyFun extends Function1[Configuration[Substitution[HOLExpression]], List[Configuration[Substitution[HOLExpression]]]] {

      def apply(conf2: Configuration[Substitution[HOLExpression]]): List[Configuration[Substitution[HOLExpression]]] = {
        implicit val disAllowedVars: MSet[Var] = MSet[Var]()
        val conf = conf2.asInstanceOf[MyConfiguration]
//        println("\n\nconf = "+conf.toStr)
        if (inPreSolvedForm(conf.uproblems)) {
//          println("terminal+result")
          (new MyConfiguration(Some(createSub(conf.uproblems))))::Nil
        }
        else conf.uproblems match {

          // (1)
          case (v,u)::uptail if u == v => List(new MyConfiguration(uptail))

          // (flex,flex)
          case (HOLVar(n1,t1), HOLVar(n2,t2))::uptail => List(new MyConfiguration(pushPreSolvedToEnd(conf.uproblems)))

          // (2)
          case (AbsN(_,AppN1(v,ls1)),AbsN(_,AppN1(u,ls2)))::uptail if v == u => (new MyConfiguration( (ls1.zip(ls2).asInstanceOf[List[Tuple2[HOLExpression,HOLExpression]]]) ::: uptail))::Nil

          // (3)
          case (AbsN(args1,AppN(f,ls1)), v @ AbsN(args2,_))::uptail if etaSimplifiedForm(args1.asInstanceOf[List[HOLExpression]], ls1.asInstanceOf[List[HOLExpression]])
               && notInFreeVarsOf(f.asInstanceOf[HOLExpression],v)
               && isHOLVar(f.asInstanceOf[HOLExpression])
               && args1.size == args2.size => {
              val sub = createSub(Pair(f, v).asInstanceOf[Pair[HOLExpression, HOLExpression]]::Nil)
              val newConf = (new MyConfiguration(pushPreSolvedToEnd((f.asInstanceOf[HOLExpression],v)::betaNormalize(applySubToListOfPairs(sub,uptail)))))
              newConf::Nil
          }

          // (3) symmetric
          case (v @ AbsN(args2,_), AbsN(args1,AppN(f,ls1)))::uptail if etaSimplifiedForm(args1.asInstanceOf[List[HOLExpression]], ls1.asInstanceOf[List[HOLExpression]])
               && notInFreeVarsOf(f.asInstanceOf[HOLExpression],v)
               && isHOLVar(f.asInstanceOf[HOLExpression])
               && args1.size == args2.size => {
              val sub = createSub(Pair(f, v).asInstanceOf[Pair[HOLExpression, HOLExpression]]::Nil)
              val newConf = (new MyConfiguration(pushPreSolvedToEnd((f.asInstanceOf[HOLExpression],v)::betaNormalize(applySubToListOfPairs(sub,uptail)))))
              newConf::Nil
          }

          // (4ab)
          case (t1 @ AbsN(args1,AppN1(f,ls1)), t2 @ AbsN(args2,AppN1(a,ls2)))::rest if isHOLVar(f.asInstanceOf[HOLExpression]) && (isFreeVarIn(a.asInstanceOf[HOLExpression], t2) || isFunctionConstantSymbol(a.asInstanceOf[HOLExpression]) )=> {// (4)
                //4a
                val imitation = pairPartialBindingImitation(Tuple2(t1, t2)::rest)._2

                ( //4b
                  if (isFunctionConstantSymbol(a.asInstanceOf[HOLExpression]) || args2.contains(a)) {
//                    println("\nimitation + projection")
                    val rez = imitation ::: listOfProjections((t1, t2)::rest)
//                    rez.foreach(x => println(x.asInstanceOf[MyConfiguration].toStr))
                    rez
                  }
                  else {
//                    println("\nonly imitation ")
                    imitation.foreach(x => println(x.asInstanceOf[MyConfiguration].toStr))
                    imitation ::: List()
                  }
                )
          }

          // (4ab) symmetric
          case (t2 @ AbsN(args2,AppN1(a,ls2)), t1 @ AbsN(args1,AppN1(f,ls1)))::rest if isHOLVar(f.asInstanceOf[HOLExpression]) && (isFreeVarIn(a.asInstanceOf[HOLExpression], t2) || isFunctionConstantSymbol(a.asInstanceOf[HOLExpression]) )=> {// (4)
            //4a
              val imitation = pairPartialBindingImitation((t1, t2)::rest)._2

              ( //4b
                if (isFunctionConstantSymbol(a.asInstanceOf[HOLExpression]) || args2.contains(a)) {
  //                  println("\nimitation + projection")
                  val rez = imitation ::: listOfProjections((t1, t2)::rest)
                  rez.foreach(x => println(x.asInstanceOf[MyConfiguration].toStr))
                  rez
                }
                else {
  //                  println("\nonly imitation ")
                  imitation.foreach(x => println(x.asInstanceOf[MyConfiguration].toStr))
                  imitation ::: List()
                }
              )
          }
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
            if (e.freeVariables.contains(v.asInstanceOf[Var]) || e.boundVariables.contains(v.asInstanceOf[Var]))
              return false
            rest.foreach(x =>
              if (x._1.freeVariables.contains(v.asInstanceOf[Var]) || x._1.boundVariables.contains(v.asInstanceOf[Var]) || x._2.freeVariables.contains(v.asInstanceOf[Var]) || x._2.boundVariables.contains(v.asInstanceOf[Var]))
                return false
                        )
            inPreSolvedForm(ls.tail)
          }
          case (e: HOLExpression, v @ HOLVar(n1,t1))  =>{
            if (e.freeVariables.contains(v.asInstanceOf[Var]) || e.boundVariables.contains(v.asInstanceOf[Var]))
              return false
            rest.foreach(x =>
              if (x._1.freeVariables.contains(v.asInstanceOf[Var]) || x._1.boundVariables.contains(v.asInstanceOf[Var]) || x._2.freeVariables.contains(v.asInstanceOf[Var]) || x._2.boundVariables.contains(v.asInstanceOf[Var]))
                return false
                        )
            inPreSolvedForm(ls.tail)
          }
          case _ => {
//            println("inPreSolvedForm == false")
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

    private[huet] def etaSimplifiedForm(ls1: List[HOLExpression],ls2: List[HOLExpression]): Boolean = {
      if (ls1.size != ls2.size)
        return false
      val lls = etaBetaNormalization(ls1.zip(ls2))
      lls.foreach(x => {
        if(x._1 != x._2)
          return false
      })
      return true

    }
    private[huet] def notInFreeVarsOf(v: HOLExpression, u: HOLExpression): Boolean = !u.freeVariables.contains(v.asInstanceOf[Var])


    private[huet] def createSub(ls: List[Tuple2[HOLExpression,HOLExpression]]): Substitution[HOLExpression] = {
      val map: Map[Var, HOLExpression] = new HashMap[Var, HOLExpression]()
      val new_map = ls.foldLeft(map)((x,y)=> {
        y._1 match {
          case HOLVar(n,t) => x + ((y._1.asInstanceOf[Var], y._2.asInstanceOf[HOLExpression]))
          case _ => x + ((y._2.asInstanceOf[Var], y._1.asInstanceOf[HOLExpression]))
        }
      })
      Substitution(new_map)
    }


    private[huet] def applySubToListOfPairs(s : Substitution[HOLExpression], l : List[Tuple2[HOLExpression, HOLExpression]]) : List[Tuple2[HOLExpression, HOLExpression]] = {
        return l.map(a => (BetaReduction.betaNormalize(s.apply(a._1))(Outermost).asInstanceOf[HOLExpression], BetaReduction.betaNormalize(s.apply(a._2))(Outermost).asInstanceOf[HOLExpression]))
    }


    private[huet] def betaNormalize(exp: List[Pair[HOLExpression,HOLExpression]]): List[Pair[HOLExpression,HOLExpression]] = {
      exp.map(x => (BetaReduction.betaNormalize(x._1 )(Outermost).asInstanceOf[HOLExpression], BetaReduction.betaNormalize(x._2 )(Outermost).asInstanceOf[HOLExpression]))
    }

    private[huet] def isFreeVarIn(v : HOLExpression, t1: HOLExpression): Boolean = {
      !t1.boundVariables.contains(v.asInstanceOf[Var])
    }

    private[huet] def isFunctionConstantSymbol(v: HOLExpression): Boolean ={
      v match {
        case HOLConst(n,t) => true
        case _ => false
      }
    }

    private[huet] def isHOLVar(f: HOLExpression): Boolean = f match {
      case HOLVar(n,t) => true
      case _ => false
    }

    def applySubToListOfPairs(l : List[Tuple2[HOLExpression, HOLExpression]], s : Substitution[HOLExpression]) : List[Tuple2[HOLExpression, HOLExpression]] = {
        return l.map(a => (BetaReduction.betaNormalize(s.apply(a._1))(Outermost).asInstanceOf[HOLExpression], BetaReduction.betaNormalize(s.apply(a._2))(Outermost).asInstanceOf[HOLExpression]))
    }

    def etaBetaNormalization(uprobl : List[Pair[HOLExpression, HOLExpression]]) : List[Pair[HOLExpression, HOLExpression]] = {
      uprobl.map(x => Tuple2(BetaReduction.betaNormalize(EtaNormalize(x._1)(MSet[Var]()))(Outermost) , BetaReduction.betaNormalize(EtaNormalize(x._2)(MSet[Var]()))(Outermost))).asInstanceOf[List[Pair[HOLExpression, HOLExpression]]]
    }


    private[huet] def createFuncVarH(ys: List[HOLVar], ls: List[HOLVar])(implicit disAllowedVars: MSet[Var] ) : Var = {
      val k: HOLVar = HOLVar(VariableStringSymbol("x"), Ti()).asInstanceOf[HOLVar]
      val dv  = disAllowedVars.foldLeft(Set[Var]())((ls,x) => ls.+(x))
      val fv: Var = freshVar.apply1(FunctionType.apply(Ti(), (ys:::ls).map(x => x.exptype)), dv, k)
      disAllowedVars.union(fv.freeVariables)
      disAllowedVars.union(fv.boundVariables)
      disAllowedVars.+(fv)
      fv
    }

    private[huet] def getListOfZs(exptype: TA)(implicit disAllowedVars: MSet[Var] ) : List[HOLVar] = {
      val k = HOLVar(VariableStringSymbol("x"), Ti())
      val l1 = List[HOLVar]()
      exptype match {
        case Ti() => {
           val dv  = disAllowedVars.foldLeft(Set[Var]())((ls,x) => ls.+(x))
           val fv = freshVar.apply1(exptype ,dv, k ).asInstanceOf[HOLVar]
           disAllowedVars.+(fv);
           disAllowedVars.union(fv.freeVariables)
           disAllowedVars.union(fv.boundVariables)
           return l1
        }
        case FunctionType(to, lsArgs ) => {
          val ls:List[HOLVar] = lsArgs.map(z => {
            val dv  = disAllowedVars.foldLeft(Set[Var]())((ls,x) => ls.+(x))
            val fv = freshVar.apply1(z, dv, k); disAllowedVars.+(fv);
            disAllowedVars.union(fv.freeVariables)
            disAllowedVars.union(fv.boundVariables)
            fv.asInstanceOf[HOLVar]
          })
          ls
        }
        case _ => { println("\n ERROR in getListOfZs \n"); l1}
      }
    }

  //4a
  private[huet] def pairPartialBindingImitation(uprobl : List[Pair[HOLExpression, HOLExpression]])(implicit disAllowedVars: MSet[Var] ) :  Tuple2[HOLExpression, List[Configuration[Substitution[HOLExpression]]]] = {
    uprobl match {
      case (AbsN(varList1, AppN(funcVar: HOLVar, args1)), AbsN(varList2, Function(sym : ConstantStringSymbol, args2, returnType)))::s => {

              val dv  = disAllowedVars.foldLeft(Set[Var]())((ls,x) => ls.+(x))
              val newVarList = args1.map(x => {val fv = freshVar.apply1(x.exptype, dv, funcVar); disAllowedVars+=fv; fv} )
              val generalFlexibleTermList = args2.map(x1 => createFuncVarH(newVarList.asInstanceOf[List[HOLVar]], getListOfZs(x1.exptype)))
              val zHlist = generalFlexibleTermList.zip(args2.map(x => getListOfZs(x.exptype))).map(x => AbsN(x._2, x._1))
              val appzHlist = zHlist.map(x => {
                val ev = EtaExpand.apply( AppN(x, newVarList));
                disAllowedVars.union(ev.freeVariables);
                disAllowedVars.union(ev.boundVariables);
                ev
              })

            val headType = FunctionType(returnType, args2.map(arg => arg.exptype))      //before returnType was the type of the head
            val term = AppN(Var(sym, headType,funcVar.factory), appzHlist)
            val part_bind_t = AbsN(newVarList, term ).asInstanceOf[HOLExpression]
            val sigma = Substitution[HOLExpression](funcVar, part_bind_t)
            val newConfNode = (new MyConfiguration((applySubToListOfPairs(uprobl, sigma)).map(x => (x._1, BetaReduction.betaNormalize(x._2 )(Outermost)).asInstanceOf[Pair[HOLExpression, HOLExpression]]) :::((funcVar,part_bind_t) ::Nil), None, false))
            Pair(part_bind_t, newConfNode::Nil)
          }
      case _ => println("\nError in 4a\n") ; sys.exit(0)
        }
    }


  // 4b
  private[huet] def listOfProjections(uprobl : List[Pair[HOLExpression, HOLExpression]])(implicit disAllowedVars: MSet[Var] ) :  List[Configuration[Substitution[HOLExpression]]] = {
    uprobl match {
        case (AbsN(varList1, AppN(funcVar: HOLVar, args1)), AbsN(varList2, AppN(funcVar2: HOLConst, args2)))::s => {
         val dv  = disAllowedVars.foldLeft(Set[Var]())((ls,x) => ls.+(x))
         val newVarList = args1.map(x => {val fv = freshVar.apply1(x.exptype, dv, funcVar).asInstanceOf[HOLVar]; disAllowedVars+=fv; fv.asInstanceOf[HOLVar]} )
         val generalFlexibleTermListOfList: List[List[HOLVar]] = newVarList.map(x => {
           x.exptype match {
             case Ti() => List[HOLVar]()
             case FunctionType(to, lsArgs ) => {
               lsArgs.map(x1 => createFuncVarH(newVarList.asInstanceOf[List[HOLVar]], getListOfZs(x1)).asInstanceOf[HOLVar])
             }
           }
         })

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
         val listOfY_i = (newVarList.zip(listOfArgsOfY_i)).map(x => {
           x._2 match {
             case List() => x._1
             case _   => {println("\nx._1.exptype = "+x._1.exptype); println("\nx._2 list = "+x._2.head.exptype.toString); AppN(x._1,x._2)}
           }
         })
         val listOfPartBindings = (newVarList.zip(listOfY_i)).map(x => {
           x._2 match {
             case List() => AbsN(newVarList, x._1).asInstanceOf[HOLExpression]
             case _ => AbsN(newVarList, x._2).asInstanceOf[HOLExpression]
           }
         })
         val listOfSubstPartBindPair = (listOfPartBindings.map(x => Substitution[HOLExpression](funcVar, x))).zip(listOfPartBindings)
         val llist = listOfSubstPartBindPair.map(x => Tuple2(applySubToListOfPairs(s,x._1), x._2))
         val newl = llist.map(x => {
           val sigma = Substitution[HOLExpression](funcVar, x._2);
           new MyConfiguration(applySubToListOfPairs( uprobl, sigma) :::( Pair(funcVar, x._2)::Nil))
           })
         return newl
        }
      case _ =>  println("\nError in 4b\n"); sys.exit(1)
      }
    }
  }
}
*/
