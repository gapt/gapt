/*
 * FOLUnificationAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.unification.fol

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.algorithms.unification.UnificationAlgorithm
import at.logic.language.fol._
import at.logic.language.lambda.substitutions.Substitution

object FOLUnificationAlgorithm extends UnificationAlgorithm[FOLExpression] {
  def unify(term1: FOLExpression, term2: FOLExpression) = {
    unifySetOfTuples(Tuple2(term1.asInstanceOf[FOLExpression],term2.asInstanceOf[FOLExpression])::Nil,Nil) match {
      case Some((Nil,ls)) => List(Substitution[FOLExpression](ls.map(x => (x._1.asInstanceOf[FOLVar],x._2))))
      case _ => Nil
    }
  }

  def applySubToListOfPairs(l : List[Tuple2[FOLExpression, FOLExpression]], s : Substitution[FOLExpression]) : List[Tuple2[FOLExpression, FOLExpression]] = {
  //  l.foldLeft(Nil)((Tuple2(x,v))=> (Tuple2(s.applyFOL(x),s.applyFOL(v))))
    return l.map(a => (s.apply(a._1), s.apply(a._2)))
  }

  def isSolvedVarIn(x : FOLVar, l : List[Tuple2[FOLExpression, FOLExpression]]) : Boolean = {
      for ( term <- ((l.map((a)=>a._1)) ::: (l.map((a)=>a._2))))
        if(getVars(term).contains(x))
            false
      true

  }

  def getVars(f: FOLExpression): List[FOLVar] = f match {
      case (FOLConst(c)) => Nil
      case (t1 @ FOLVar(x)) => t1.asInstanceOf[FOLVar]::Nil
      case (function @ Function(_, args @ _)) => args.flatMap( a => getVars(a) )
  }

  def unifySetOfTuples(s1: List[Tuple2[FOLExpression, FOLExpression]], s2 : List[Tuple2[FOLExpression, FOLExpression]]) : Option[(List[Tuple2[FOLExpression, FOLExpression]], List[Tuple2[FOLExpression, FOLExpression]])] = (s1,s2) match {
    case (((a1,a2)::s), s2) if a1 == a2 => unifySetOfTuples(s, s2)

    case ((FOLConst (name1),FOLConst (name2))::s,s2) if name1 != name2 => None
    case (((Function(f1,args1), Function(f2, args2)):: (s)), s2)
      if args1.length == args2.length && f1==f2  => {
          return unifySetOfTuples(args1.zip(args2) ::: s, s2)
      }
    case (((Atom(f1,args1), Atom(f2, args2)):: (s)), s2)
      if args1.length == args2.length && f1==f2  => {
          return unifySetOfTuples(args1.zip(args2) ::: s, s2)
      }

    case (((x : FOLVar,v)::s), s2) if !getVars(v).contains(x) =>
      //  x does not occur in v && x is not in solved form =>
   //   print(applySubToListOfPairs(s,Substitution(x,v)).toString+"\n")
        unifySetOfTuples(applySubToListOfPairs(s,Substitution[FOLExpression](x,v)), (x,v)::applySubToListOfPairs(s2,Substitution[FOLExpression](x,v)))


    case (((v, x : FOLVar)::s), s2) if !getVars(v).contains(x) =>
        unifySetOfTuples(applySubToListOfPairs(s,Substitution[FOLExpression](x,v)), (x,v)::applySubToListOfPairs(s2,Substitution[FOLExpression](x,v)))
    case (Nil, s2) => Some((Nil, s2))
    case _ => None
  }
}