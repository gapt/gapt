/*
Fixing this seems to require a better understanding of the algorithm due to the
extensive use of AppN (which no longer exists). Since it is not being used anywhere, I am commenting
it out for now. [Giselle]

package at.logic.gapt.language.hol.algorithms.unification.hol

package huet {

import at.logic.gapt.expr.etaExpansion._
import scala.collection.immutable.HashMap
import at.logic.gapt.utils.executionModels.searchAlgorithms.BFSAlgorithm
import at.logic.gapt.expr. {->, Ti, TA, FunctionType}
import at.logic.gapt.expr.VariableStringSymbol
import at.logic.gapt.expr.typedLambdaCalculus._
import at.logic.gapt.language.hol.algorithms.unification.UnificationAlgorithm
import at.logic.gapt.language.hol._
import at.logic.gapt.language.hol.LambdaExpression
import at.logic.gapt.language.hol.logicSymbols._
import at.logic.gapt.expr.substitutions.Substitution
import at.logic.gapt.expr.etaExpansion.EtaExpand
import scala.collection.mutable.{Set => MSet}
import at.logic.gapt.utils.executionModels.ndStream.{NDStream, Configuration}
import at.logic.gapt.expr.BetaReduction._
import at.logic.gapt.expr.BetaReduction

//import at.logic.gapt.expr
  import StrategyOuterInner._
  import StrategyLeftRight._

  private[huet] class MyConfiguration(val uproblems: List[Tuple2[LambdaExpression,LambdaExpression]], val result: Option[Substitution[LambdaExpression]], val isTerminal: Boolean) extends Configuration[Substitution[LambdaExpression]] {
        def this() = this(List(), None, true) // for failure
        def this(result: Option[Substitution[LambdaExpression]]) = this(List(), result, true) // for success
        def this(l: List[Tuple2[LambdaExpression,LambdaExpression]]) = this(l, None, false) // for in node
        def toStr  = uproblems.map(x => ("<"+x._1.toStringSimple+", "+ x._2.toStringSimple+">"))
  }



  object Huet {

    def apply(uproblems: List[Tuple2[LambdaExpression,LambdaExpression]]): NDStream[Substitution[LambdaExpression]] =
      if (!validateTypes(uproblems))
        throw new IllegalArgumentException("Types of pairs do not match")
      else {
        new NDStream[Substitution[LambdaExpression]](new MyConfiguration(etaBetaNormalization(uproblems), None, false), MyFun) with BFSAlgorithm
      }

    def apply(e1 : LambdaExpression, e2 : LambdaExpression): NDStream[Substitution[LambdaExpression]] = apply((e1,e2)::Nil)



    private[huet] object MyFun extends Function1[Configuration[Substitution[LambdaExpression]], List[Configuration[Substitution[LambdaExpression]]]] {

      def apply(conf2: Configuration[Substitution[LambdaExpression]]): List[Configuration[Substitution[LambdaExpression]]] = {
        implicit val disAllowedVars: MSet[Var] = MSet[Var]()
        val conf = conf2.asInstanceOf[MyConfiguration]
        val nLine = sys.props("line.separator")      
//        println( nLine + nLine + "conf = "+conf.toStr)
        if (inPreSolvedForm(conf.uproblems)) {
//          println("terminal+result")
          (new MyConfiguration(Some(createSub(conf.uproblems))))::Nil
        }
        else conf.uproblems match {

          // (1)
          case (v,u)::uptail if u == v => List(new MyConfiguration(uptail))

          // (flex,flex)
          case (Var(n1,t1), Var(n2,t2))::uptail => List(new MyConfiguration(pushPreSolvedToEnd(conf.uproblems)))

          // (2)
          case (AbsN(_,AppN1(v,ls1)),AbsN(_,AppN1(u,ls2)))::uptail if v == u => (new MyConfiguration( (ls1.zip(ls2).asInstanceOf[List[Tuple2[LambdaExpression,LambdaExpression]]]) ::: uptail))::Nil

          // (3)
          case (AbsN(args1,AppN(f,ls1)), v @ AbsN(args2,_))::uptail if etaSimplifiedForm(args1.asInstanceOf[List[LambdaExpression]], ls1.asInstanceOf[List[LambdaExpression]])
               && notInFreeVarsOf(f.asInstanceOf[LambdaExpression],v)
               && isVar(f.asInstanceOf[LambdaExpression])
               && args1.size == args2.size => {
              val sub = createSub(Pair(f, v).asInstanceOf[Pair[LambdaExpression, LambdaExpression]]::Nil)
              val newConf = (new MyConfiguration(pushPreSolvedToEnd((f.asInstanceOf[LambdaExpression],v)::betaNormalize(applySubToListOfPairs(sub,uptail)))))
              newConf::Nil
          }

          // (3) symmetric
          case (v @ AbsN(args2,_), AbsN(args1,AppN(f,ls1)))::uptail if etaSimplifiedForm(args1.asInstanceOf[List[LambdaExpression]], ls1.asInstanceOf[List[LambdaExpression]])
               && notInFreeVarsOf(f.asInstanceOf[LambdaExpression],v)
               && isVar(f.asInstanceOf[LambdaExpression])
               && args1.size == args2.size => {
              val sub = createSub(Pair(f, v).asInstanceOf[Pair[LambdaExpression, LambdaExpression]]::Nil)
              val newConf = (new MyConfiguration(pushPreSolvedToEnd((f.asInstanceOf[LambdaExpression],v)::betaNormalize(applySubToListOfPairs(sub,uptail)))))
              newConf::Nil
          }

          // (4ab)
          case (t1 @ AbsN(args1,AppN1(f,ls1)), t2 @ AbsN(args2,AppN1(a,ls2)))::rest if isVar(f.asInstanceOf[LambdaExpression]) && (isFreeVarIn(a.asInstanceOf[LambdaExpression], t2) || isFunctionConstantSymbol(a.asInstanceOf[LambdaExpression]) )=> {// (4)
                //4a
                val imitation = pairPartialBindingImitation(Tuple2(t1, t2)::rest)._2

                ( //4b
                  if (isFunctionConstantSymbol(a.asInstanceOf[LambdaExpression]) || args2.contains(a)) {
//                    println( nLine + "imitation + projection")
                    val rez = imitation ::: listOfProjections((t1, t2)::rest)
//                    rez.foreach(x => println(x.asInstanceOf[MyConfiguration].toStr))
                    rez
                  }
                  else {
//                    println( nLine + "only imitation ")
                    imitation.foreach(x => println(x.asInstanceOf[MyConfiguration].toStr))
                    imitation ::: List()
                  }
                )
          }

          // (4ab) symmetric
          case (t2 @ AbsN(args2,AppN1(a,ls2)), t1 @ AbsN(args1,AppN1(f,ls1)))::rest if isVar(f.asInstanceOf[LambdaExpression]) && (isFreeVarIn(a.asInstanceOf[LambdaExpression], t2) || isFunctionConstantSymbol(a.asInstanceOf[LambdaExpression]) )=> {// (4)
            //4a
              val imitation = pairPartialBindingImitation((t1, t2)::rest)._2

              ( //4b
                if (isFunctionConstantSymbol(a.asInstanceOf[LambdaExpression]) || args2.contains(a)) {
  //                  println( nLine + "imitation + projection")
                  val rez = imitation ::: listOfProjections((t1, t2)::rest)
                  rez.foreach(x => println(x.asInstanceOf[MyConfiguration].toStr))
                  rez
                }
                else {
  //                  println( nLine + "only imitation ")
                  imitation.foreach(x => println(x.asInstanceOf[MyConfiguration].toStr))
                  imitation ::: List()
                }
              )
          }
          case _ => List()
       }
      }
    }

    private[huet] def validateTypes(ls: List[Tuple2[LambdaExpression,LambdaExpression]]): Boolean = ls match {
      case x::rest => x._1.exptype == x._2.exptype && validateTypes(rest)
      case _ => true
    }



    private[huet] def inPreSolvedForm(ls: List[Tuple2[LambdaExpression,LambdaExpression]]): Boolean = ls match {
      case head::rest => {
        head match {
          case (Var(n1,t1), Var(n2,t2)) => inPreSolvedForm(rest)
          case (v @ Var(n1,t1), e: LambdaExpression)   => {
            if (e.freeVariables.contains(v.asInstanceOf[Var]) || e.boundVariables.contains(v.asInstanceOf[Var]))
              return false
            rest.foreach(x =>
              if (x._1.freeVariables.contains(v.asInstanceOf[Var]) || x._1.boundVariables.contains(v.asInstanceOf[Var]) || x._2.freeVariables.contains(v.asInstanceOf[Var]) || x._2.boundVariables.contains(v.asInstanceOf[Var]))
                return false
                        )
            inPreSolvedForm(ls.tail)
          }
          case (e: LambdaExpression, v @ Var(n1,t1))  =>{
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

    private[huet] def pushPreSolvedToEnd(l: List[Tuple2[LambdaExpression,LambdaExpression]]): List[Tuple2[LambdaExpression,LambdaExpression]] = l match {
      case x::rest => rest:::(x::Nil)
      case _ => l
    }

    private[huet] def etaSimplifiedForm(ls1: List[LambdaExpression],ls2: List[LambdaExpression]): Boolean = {
      if (ls1.size != ls2.size)
        return false
      val lls = etaBetaNormalization(ls1.zip(ls2))
      lls.foreach(x => {
        if(x._1 != x._2)
          return false
      })
      return true

    }
    private[huet] def notInFreeVarsOf(v: LambdaExpression, u: LambdaExpression): Boolean = !u.freeVariables.contains(v.asInstanceOf[Var])


    private[huet] def createSub(ls: List[Tuple2[LambdaExpression,LambdaExpression]]): Substitution[LambdaExpression] = {
      val map: Map[Var, LambdaExpression] = new HashMap[Var, LambdaExpression]()
      val new_map = ls.foldLeft(map)((x,y)=> {
        y._1 match {
          case Var(n,t) => x + ((y._1.asInstanceOf[Var], y._2.asInstanceOf[LambdaExpression]))
          case _ => x + ((y._2.asInstanceOf[Var], y._1.asInstanceOf[LambdaExpression]))
        }
      })
      Substitution(new_map)
    }


    private[huet] def applySubToListOfPairs(s : Substitution[LambdaExpression], l : List[Tuple2[LambdaExpression, LambdaExpression]]) : List[Tuple2[LambdaExpression, LambdaExpression]] = {
        return l.map(a => (BetaReduction.betaNormalize(s.apply(a._1))(Outermost).asInstanceOf[LambdaExpression], BetaReduction.betaNormalize(s.apply(a._2))(Outermost).asInstanceOf[LambdaExpression]))
    }


    private[huet] def betaNormalize(exp: List[Pair[LambdaExpression,LambdaExpression]]): List[Pair[LambdaExpression,LambdaExpression]] = {
      exp.map(x => (BetaReduction.betaNormalize(x._1 )(Outermost).asInstanceOf[LambdaExpression], BetaReduction.betaNormalize(x._2 )(Outermost).asInstanceOf[LambdaExpression]))
    }

    private[huet] def isFreeVarIn(v : LambdaExpression, t1: LambdaExpression): Boolean = {
      !t1.boundVariables.contains(v.asInstanceOf[Var])
    }

    private[huet] def isFunctionConstantSymbol(v: LambdaExpression): Boolean ={
      v match {
        case Const(n,t) => true
        case _ => false
      }
    }

    private[huet] def isVar(f: LambdaExpression): Boolean = f match {
      case Var(n,t) => true
      case _ => false
    }

    def applySubToListOfPairs(l : List[Tuple2[LambdaExpression, LambdaExpression]], s : Substitution[LambdaExpression]) : List[Tuple2[LambdaExpression, LambdaExpression]] = {
        return l.map(a => (BetaReduction.betaNormalize(s.apply(a._1))(Outermost).asInstanceOf[LambdaExpression], BetaReduction.betaNormalize(s.apply(a._2))(Outermost).asInstanceOf[LambdaExpression]))
    }

    def etaBetaNormalization(uprobl : List[Pair[LambdaExpression, LambdaExpression]]) : List[Pair[LambdaExpression, LambdaExpression]] = {
      uprobl.map(x => Tuple2(BetaReduction.betaNormalize(EtaNormalize(x._1)(MSet[Var]()))(Outermost) , BetaReduction.betaNormalize(EtaNormalize(x._2)(MSet[Var]()))(Outermost))).asInstanceOf[List[Pair[LambdaExpression, LambdaExpression]]]
    }


    private[huet] def createFuncVarH(ys: List[Var], ls: List[Var])(implicit disAllowedVars: MSet[Var] ) : Var = {
      val k: Var = Var(VariableStringSymbol("x"), Ti()).asInstanceOf[Var]
      val dv  = disAllowedVars.foldLeft(Set[Var]())((ls,x) => ls.+(x))
      val fv: Var = freshVar.apply1(FunctionType.apply(Ti(), (ys:::ls).map(x => x.exptype)), dv, k)
      disAllowedVars.union(fv.freeVariables)
      disAllowedVars.union(fv.boundVariables)
      disAllowedVars.+(fv)
      fv
    }

    private[huet] def getListOfZs(exptype: TA)(implicit disAllowedVars: MSet[Var] ) : List[Var] = {
      val k = Var(VariableStringSymbol("x"), Ti())
      val l1 = List[Var]()
      exptype match {
        case Ti() => {
           val dv  = disAllowedVars.foldLeft(Set[Var]())((ls,x) => ls.+(x))
           val fv = freshVar.apply1(exptype ,dv, k ).asInstanceOf[Var]
           disAllowedVars.+(fv);
           disAllowedVars.union(fv.freeVariables)
           disAllowedVars.union(fv.boundVariables)
           return l1
        }
        case FunctionType(to, lsArgs ) => {
          val ls:List[Var] = lsArgs.map(z => {
            val dv  = disAllowedVars.foldLeft(Set[Var]())((ls,x) => ls.+(x))
            val fv = freshVar.apply1(z, dv, k); disAllowedVars.+(fv);
            disAllowedVars.union(fv.freeVariables)
            disAllowedVars.union(fv.boundVariables)
            fv.asInstanceOf[Var]
          })
          ls
        }
        case _ => { println( sys.props("line.separator") + " ERROR in getListOfZs " + sys.props("line.separator") ); l1}
      }
    }

  //4a
  private[huet] def pairPartialBindingImitation(uprobl : List[Pair[LambdaExpression, LambdaExpression]])(implicit disAllowedVars: MSet[Var] ) :  Tuple2[LambdaExpression, List[Configuration[Substitution[LambdaExpression]]]] = {
    uprobl match {
      case (AbsN(varList1, AppN(funcVar: Var, args1)), AbsN(varList2, Function(sym : ConstantStringSymbol, args2, returnType)))::s => {

              val dv  = disAllowedVars.foldLeft(Set[Var]())((ls,x) => ls.+(x))
              val newVarList = args1.map(x => {val fv = freshVar.apply1(x.exptype, dv, funcVar); disAllowedVars+=fv; fv} )
              val generalFlexibleTermList = args2.map(x1 => createFuncVarH(newVarList.asInstanceOf[List[Var]], getListOfZs(x1.exptype)))
              val zHlist = generalFlexibleTermList.zip(args2.map(x => getListOfZs(x.exptype))).map(x => AbsN(x._2, x._1))
              val appzHlist = zHlist.map(x => {
                val ev = EtaExpand.apply( AppN(x, newVarList));
                disAllowedVars.union(ev.freeVariables);
                disAllowedVars.union(ev.boundVariables);
                ev
              })

            val headType = FunctionType(returnType, args2.map(arg => arg.exptype))      //before returnType was the type of the head
            val term = AppN(Var(sym, headType,funcVar.factory), appzHlist)
            val part_bind_t = AbsN(newVarList, term ).asInstanceOf[LambdaExpression]
            val sigma = Substitution[LambdaExpression](funcVar, part_bind_t)
            val newConfNode = (new MyConfiguration((applySubToListOfPairs(uprobl, sigma)).map(x => (x._1, BetaReduction.betaNormalize(x._2 )(Outermost)).asInstanceOf[Pair[LambdaExpression, LambdaExpression]]) :::((funcVar,part_bind_t) ::Nil), None, false))
            Pair(part_bind_t, newConfNode::Nil)
          }
      case _ => println( sys.props("line.separator") + "Error in 4a" + sys.props("line.separator") ) ; sys.exit(0)
        }
    }


  // 4b
  private[huet] def listOfProjections(uprobl : List[Pair[LambdaExpression, LambdaExpression]])(implicit disAllowedVars: MSet[Var] ) :  List[Configuration[Substitution[LambdaExpression]]] = {
    uprobl match {
        case (AbsN(varList1, AppN(funcVar: Var, args1)), AbsN(varList2, AppN(funcVar2: Const, args2)))::s => {
         val dv  = disAllowedVars.foldLeft(Set[Var]())((ls,x) => ls.+(x))
         val newVarList = args1.map(x => {val fv = freshVar.apply1(x.exptype, dv, funcVar).asInstanceOf[Var]; disAllowedVars+=fv; fv.asInstanceOf[Var]} )
         val generalFlexibleTermListOfList: List[List[Var]] = newVarList.map(x => {
           x.exptype match {
             case Ti() => List[Var]()
             case FunctionType(to, lsArgs ) => {
               lsArgs.map(x1 => createFuncVarH(newVarList.asInstanceOf[List[Var]], getListOfZs(x1)).asInstanceOf[Var])
             }
           }
         })

         val listOfArgsOfY_i = generalFlexibleTermListOfList.zip(newVarList).map(x => {
           x._1 match {
             case Nil => List[Var]()
             case _ => {
               x._2.exptype match {
                 case FunctionType(to, lsArgs ) =>  (x._1.zip(lsArgs)).map(y => {val zs = getListOfZs(y._2) ;val h = AbsN(zs, AppN(AppN(y._1, newVarList), zs)); println( sys.props("line.separator") + "h = "+h.toString1+"  :  "+h.exptype.toString ); h})
                 case Ti() => {println( sys.props("line.separator") + "ERROR in 2" + sys.props("line.separator") ); List[Var]()}
                 }
             }
           }
         })
         val listOfY_i = (newVarList.zip(listOfArgsOfY_i)).map(x => {
           x._2 match {
             case List() => x._1
             case _   => {println( sys.props("line.separator") + "x._1.exptype = "+x._1.exptype); println( sys.props("line.separator") + "x._2 list = "+x._2.head.exptype.toString); AppN(x._1,x._2)}
           }
         })
         val listOfPartBindings = (newVarList.zip(listOfY_i)).map(x => {
           x._2 match {
             case List() => AbsN(newVarList, x._1).asInstanceOf[LambdaExpression]
             case _ => AbsN(newVarList, x._2).asInstanceOf[LambdaExpression]
           }
         })
         val listOfSubstPartBindPair = (listOfPartBindings.map(x => Substitution[LambdaExpression](funcVar, x))).zip(listOfPartBindings)
         val llist = listOfSubstPartBindPair.map(x => Tuple2(applySubToListOfPairs(s,x._1), x._2))
         val newl = llist.map(x => {
           val sigma = Substitution[LambdaExpression](funcVar, x._2);
           new MyConfiguration(applySubToListOfPairs( uprobl, sigma) :::( Pair(funcVar, x._2)::Nil))
           })
         return newl
        }
      case _ =>  println( sys.props("line.separator") + "Error in 4b" + sys.props("line.separator") ); sys.exit(1)
      }
    }
  }
}
*/
