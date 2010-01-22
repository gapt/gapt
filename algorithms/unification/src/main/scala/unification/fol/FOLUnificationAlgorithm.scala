/*
 * FOLUnificationAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.unification.fol

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.fol.substitutions._
import at.logic.unification.UnificationAlgorithm
import at.logic.language.fol._

object FOLUnificationAlgorithm extends UnificationAlgorithm {
  def unifiy(term1: LambdaExpression, term2: LambdaExpression) = {
    require(term1.isInstanceOf[FOLTerm] && term2.isInstanceOf[FOLTerm])
 //   Substitution(unifySetOfTuples(Tuple2(term1.asInstanceOf[FOLTerm],term2.asInstanceOf[FOLTerm])::Nil))
        //Some(Substitution())
    None
  }

 def applySubToListOfPairs(l : List[Tuple2[FOLTerm, FOLTerm]], s : Substitution) : List[Tuple2[FOLTerm, FOLTerm]] =
    {
    //  l.foldLeft(Nil)((Tuple2(x,v))=> (Tuple2(s.applyFOL(x),s.applyFOL(v))))
      l.map((a) => (s.applyFOL(a._1), s.applyFOL(a._2)))
      return l;
    }

  def isSolvedVarIn(x : FOLVar, l : List[Tuple2[FOLTerm, FOLTerm]]) : Boolean =
  {
      for ( term <- ((l.map((a)=>a._1)) ::: (l.map((a)=>a._2))))
        if(getVars(term).contains(x))
            false
      true

  }

  def getVars(f: FOLTerm): List[FOLVar] = f match
  {
      case (FOLConst(c)) => Nil
      case (t1 @ FOLVar(x)) => t1.asInstanceOf[FOLVar]::Nil
      case (function @ Function(_, args @ _)) => args.flatMap( a => getVars(a) )
  }

  def unifySetOfTuples(s1: List[Tuple2[FOLTerm, FOLTerm]], s2 : List[Tuple2[FOLTerm, FOLTerm]]) : Option[(List[Tuple2[FOLTerm, FOLTerm]], List[Tuple2[FOLTerm, FOLTerm]])] = (s1,s2) match
  {
    case (((a1,a2)::s), s2) if a1 == a2 => unifySetOfTuples(s, s2)
    case (((Function(f1,args1), Function(f2, args2)):: (s : List[Tuple2[FOLTerm, FOLTerm]])), s2)
      if args1.length == args2.length && f1==f2  =>
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
}