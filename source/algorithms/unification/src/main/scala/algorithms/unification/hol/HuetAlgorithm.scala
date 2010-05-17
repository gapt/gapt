/*
 * HuetAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.unification.hol

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.algorithms.unification.UnificationAlgorithm
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.substitutions.Substitution

object rigidTerm
{
  def unapply(exp: HOLExpression) : Option[HOLExpression] = exp match
  {
    case Function(sym: ConstantStringSymbol, args, returnType) => Some(exp)
    case AbsN(varList , lambdaExp) => lambdaExp match
      {
        case AppN(f, args) if varList.contains(f) => Some(exp)
        case _ => (None)
      }
    case _ => (None)
  }
}

object HuetAlgorithm extends UnificationAlgorithm[HOLExpression]
{
    def unify(term1: HOLExpression, term2: HOLExpression) : List[Substitution[HOLExpression]] = {
      unifySetOfTuples(List[(HOLExpression,HOLExpression)](Tuple2(term1.asInstanceOf[HOLExpression],term2.asInstanceOf[HOLExpression])),Nil) match {
        case Some((Nil,ls)) => List(Substitution[HOLExpression](ls.map(x => (x._1.asInstanceOf[HOLVar],x._2))))
        case _ => Nil
      }
    }
    
    def applySubToListOfPairs(l : List[Tuple2[HOLExpression, HOLExpression]], s : Substitution[HOLExpression]) : List[Tuple2[HOLExpression, HOLExpression]] =
    {
    //  l.foldLeft(Nil)((Tuple2(x,v))=> (Tuple2(s.applyFOL(x),s.applyFOL(v))))
      return l.map((a) => (s.apply(a._1), s.apply(a._2)))
    }

    def unifySetOfTuples(s1: List[Tuple2[HOLExpression, HOLExpression]], s2 : List[Tuple2[HOLExpression,HOLExpression]]) : Option[(List[Tuple2[HOLExpression,HOLExpression]], List[Tuple2[HOLExpression,HOLExpression]])] = (s1,s2) match
    {
        //rule (1)
        case (((a1,a2)::s), s2) if a1 == a2 => unifySetOfTuples(s, s2)

        //rule (2')
        case ((AbsN(varList1, Function(sym1 : ConstantStringSymbol, args1, returnType1)),AbsN(varList2, Function(sym2 : ConstantStringSymbol, args2, returnType2)))::s, s2)
          if sym1 == sym2 && varList1.size == varList2.size && returnType1 == returnType2 =>
          {
            val l = args1.map(x => AbsN(varList1,x)).zip(args2.map(x => AbsN(varList2,x))):::s
            unifySetOfTuples(l.asInstanceOf[List[Tuple2[HOLExpression, HOLExpression]]],s2.asInstanceOf[List[Tuple2[HOLExpression, HOLExpression]]])
          }

        //rule (3)
        case ((AbsN(varList1, AppN(funcVar: HOLVar, args1)), v @ AbsN(varList2, exp))::s, s2)
          if varList1.size == varList2.size && exp.exptype == funcVar.exptype =>
          {
            val sigma = Substitution[HOLExpression](funcVar, v)
            unifySetOfTuples((funcVar,v)::applySubToListOfPairs(s,sigma), (funcVar,v)::s2)
          }

        //rule (4'a)
        case ((AbsN(varList1, AppN(funcVar: HOLVar, args1)), AbsN(varList2, Function(sym : ConstantStringSymbol, args2, returnType)))::s, s2)
          if varList1==varList2 =>
          {
            val newVarList = args1.map(x => freshVar(x.exptype, args1.asInstanceOf[Set[Var]], args1.asInstanceOf[LambdaExpression]))
            val generalFlexibleTermList = args1.map(x => freshVar(x.exptype, args1.asInstanceOf[Set[Var]], args1.asInstanceOf[LambdaExpression]))
            val newArgsList = generalFlexibleTermList.map(x => AppN(x,newVarList))
            val t: HOLExpression = AbsN(newVarList, Function(sym , args1.asInstanceOf[List[HOLExpression]], returnType)).asInstanceOf[HOLExpression]
            Some(((funcVar,t)::s1 ,s2))
          }

        //rule (4'b)
        case ((AbsN(varList1, AppN(funcVar: HOLVar, args1)), AbsN(varList2, AppN(funcVar2: HOLVar, args2)))::s, s2)
          if varList1==varList2 && varList2.contains(funcVar2)=>
          {
            val newVarList = args1.map(x => freshVar(x.exptype, args1.asInstanceOf[Set[Var]], args1.asInstanceOf[LambdaExpression]))
            val generalFlexibleTermList = args1.map(x => freshVar(x.exptype, args1.asInstanceOf[Set[Var]], args1.asInstanceOf[LambdaExpression]))
            val newArgsList = generalFlexibleTermList.map(x => AppN(x,newVarList))
            val t: HOLExpression = AbsN(newVarList, AppN(funcVar2, newArgsList)).asInstanceOf[HOLExpression]
            Some(((funcVar,t)::s1 ,s2))
          }

        case ((App(var1,exp1) , App(var2,exp2))::s, s2) =>
          {
        //    println("\n\nEvala !!!\n\n")
            (None)
          }

        case _ => (None)
    }
}
/*
      


        case ( (HOLAbs(v1: HOLVar, exp1: HOLExpression), subArg @ HOLAbs(v2: HOLVar, exp2: HOLExpression))::s  ,s2) if v1 == v2 && exp1.exptype == exp2.exptype => exp1 match
          {
            //rule (3)
            case HOLApp(f: HOLVar, arg: HOLExpression) /*if f not in FV(exp2)*/ =>
              {
                val sigma = Substitution(f,subArg)
                unifySetOfTuples((f,subArg)::applySubToListOfPairs(s,sigma), (f,subArg)::s2)
              }

            //rule (2')
            case Function(sym1 : ConstantStringSymbol, args1: List[HOLExpression], returnType1) => exp2 match
              {
                case Function(sym2 : ConstantStringSymbol, args2: List[HOLExpression], returnType2) if sym1 == sym2 && args1.size == args2.size && returnType1 == returnType2 =>
                  {
                    val l = args1.map(x => HOLAbs(v1,x)).zip(args2.map(x => HOLAbs(v1,x))):::s
                    unifySetOfTuples(l,s2)
                  }
                case AbsN(varList: List[Var] , lambdaExp) => lambdaExp match
                  {
                    case AppN(f, args) if varList.contains(f) =>
                      {
                        val l = args1.map(x => HOLAbs(v1,x)).zip(args.map(x => HOLAbs(v1,x))):::s
                        unifySetOfTuples(l,s2)
                      }
                  }

              }
          }

        //rule (4'a)
        case left @ AbsN(varList1, a @ Function(sym : ConstantStringSymbol, args1: List[HOLExpression], returnType1)) => left match
          {
            case AbsN(varList2, AppN(f : HOLVar, args2: List[HOLExpression])) if !varList2.contains(f) && varList1.size==varList2.size =>
              {
                val newVarList = args2.map(x => freshVar(x.exptype, left, left))
                val generalFlexibleTermList = args1.map(x => freshVar(x.exptype, left, left))
                val newArgsList = generalFlexibleTermList.map(x => AppN(x,newVarList))
                val t: HOLExpression = AbsN(newVarList, Function(sym , args1, returnType1)).asInstanceOf[HOLExpression]
                Some(((f,t)::s1 ,s2))
              }
          }
        case Function(sym1 : ConstantStringSymbol, args1: List[HOLExpression], returnType1) => exp2 match
          {
            case AbsN(varList, AppN(f : HOLVar, args)) if !varList.contains(f) =>
              {
                var i=0
                for(x <- varList)
                {

                }
                val l = args.map(x => HOLApp(new HOLVar(), ))
              }
          }
          
        }

      //rule (2')
        case ( (HOLAbs(v1: HOLVar, exp1: HOLExpression), subArg @ HOLAbs(v2: HOLVar, exp2: HOLExpression))::s  ,s2) if v1 == v2 && exp1.exptype == exp2.exptype => exp1 match
        case (((Function(f1,args1), Function(f2, args2)):: (s)), s2)  if args1.length == args2.length && f1==f2  =>
        {
            return unifySetOfTuples(args1.zip(args2) ::: s, s2)
        }

        case (((Atom(f1,args1), Atom(f2, args2)):: (s)), s2)  if args1.length == args2.length && f1==f2  =>
        {
            return unifySetOfTuples(args1.zip(args2) ::: s, s2)
        }

        case (((x : FOLVar,v)::s), s2) if !getVars(v).contains(x) && isSolvedVarIn(x,s) =>
      //  x does not occur in v && x is not in solved form =>
            unifySetOfTuples(applySubToListOfPairs(s,Substitution(x,v)), (x,v)::applySubToListOfPairs(s2,Substitution(x,v)))

        case (((v, x : FOLVar)::s), s2) if !getVars(v).contains(x) && isSolvedVarIn(x,s) =>
            unifySetOfTuples(applySubToListOfPairs(s,Substitution(x,v)), (x,v)::applySubToListOfPairs(s2,Substitution(x,v)))

        case (Nil, s2) => Some((Nil, s2))

        case _ => None
    }
}*/
