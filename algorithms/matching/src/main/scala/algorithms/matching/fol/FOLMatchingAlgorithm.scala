/*
 * FOLMatchingAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package at.logic.algorithms.matching.fol

import at.logic.algorithms.matching.MatchingAlgorithm
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.algorithms.unification.fol.FOLUnificationAlgorithm
import at.logic.language.lambda.substitutions._
//import at.logic.language.fol.substitutions._
import at.logic.language.fol._

object FOLMatchingAlgorithm extends MatchingAlgorithm {
  //def matchTerm(term: LambdaExpression, posInstance: LambdaExpression) = matchTermModulo(term, posInstance, getVars(posInstance.asInstanceOf[FOLExpression]))
  
  def matchTerm(term1: LambdaExpression, term2: LambdaExpression) = matchSetOfTuples(getVars(term2.asInstanceOf[FOLExpression]), Tuple2(term1.asInstanceOf[FOLExpression],term2.asInstanceOf[FOLExpression])::Nil,Nil) match {
      case Some((Nil,ls)) => Some(Substitution(ls.map(x => (x._1.asInstanceOf[FOLVar],x._2))))
      case _ => None
    }


  def matchTermModulo(term: LambdaExpression, posInstance: LambdaExpression, moduloVarList: List[Var]): Option[Substitution] = (term,posInstance) match
  {
    case (FOLVar(name1), FOLVar(name2)) if name1 == name2 => Some(MatchingSubstitution(moduloVarList))     

    case (FOLConst(name1),FOLConst (name2)) if name1 != name2 => { println("\n\n\n 2 \n\n\n"); None}
      
    case (FOLConst(name1),FOLConst (name2)) if name1 == name2 => { println("\n\n\n 3 \n\n\n"); Some(MatchingSubstitution(moduloVarList))}

/*
    case (Function(f1,args1), Function(f2, args2))
      if (args1.length == args2.length && f1==f2) =>
        {
            println("\n\n\n 5 \n\n\n");
            println("\n\n\n zip: "+ args1.zip(args2).toString +"\n\n\n");

            //val subst = args1.zip(args2).foldLeft(Some(MatchingSubstitution(moduloVarList)))
            var restrictedDomainSubst: Option[MatchingSubstitution] = Some(MatchingSubstitution(moduloVarList).asInstanceOf[MatchingSubstitution]);
            for(x <- args1.zip(args2))
            {
              if (restrictedDomainSubst == None)
               {
                 println("\n\n\n restrictedDomainSubst == None \n\n\n");
                 return None
               }
               else
               {
                 println("\n\n\n restrictedDomainSubst: "+ restrictedDomainSubst.toString +"\n\n\n");
                 val sub = matchTermModulo(restrictedDomainSubst.get(x._1),x._2, moduloVarList);
                 if(sub == None)
                      return None
                 else
                  {
                    println("\n\n\n 6 sub   " + sub.toString +"\n\n\n");
                    restrictedDomainSubst = appendSubstitutions(new MatchingSubstitution(moduloVarList, sub.get.map), restrictedDomainSubst.get)
                    if(restrictedDomainSubst == None)
                        return None
                    println("\n\n\n app: "+ restrictedDomainSubst.toString +"\n\n\n");
                    
                  }
               }
            }
            return restrictedDomainSubst
        }

  */

    case (Function(f1,args1), Function(f2, args2))
      if (args1.length == args2.length && f1==f2) =>
        {
            println("\n\n\n 5 \n\n\n");
            println("\n\n\n zip: "+ args1.zip(args2).toString +"\n\n\n");
            val subst = args1.zip(args2).foldLeft(Some(MatchingSubstitution(moduloVarList)): Option[Substitution])((restrictedDomainSubst, x) => restrictedDomainSubst match
               {
                  case Some(restrDom) => matchTermModulo(restrDom(x._1),x._2, moduloVarList) match 
                    {
                      case Some(sub) => Some(sub compose restrDom)
                      case _ => None
                    }
                  case _ => None         
               }) match {
                 case Some(s) => Some(s)
                 case _ => None
               }
               subst
        }



    case (v : FOLVar,term)   if !getVars(term.asInstanceOf[FOLExpression]).contains(v) && !moduloVarList.contains(v)  =>
      {
        println("\n\n\n 6 \n\n\n")
        println("\n\n\n" + "(" +v.toString + ", "+ term.toString+") \n\n\n")
        val sub = Some(Substitution(v.asInstanceOf[FOLVar],term))
        if(sub == None)
            None
        else
            {
              println("\n\n\n" + sub.toString + "\n\n\n")
              return sub
            }
        
      }
      //  x does not occur in v && x is not in solved form =>
   //   print(applySubToListOfPairs(s,Substitution(x,v)).toString+"\n")
        
        //matchTerm(applySubToListOfPairs(s,Substitution(x,v)), (x,v)::applySubToListOfPairs(s2,Substitution(x,v)))

    case (FOLConst(name1),_) => { println("\n\n\n 7 \n\n\n"); None}
//    case (((v, x : FOLVar)::s), s2) if !getVars(v).contains(x) =>
//        unifySetOfTuples(applySubToListOfPairs(s,Substitution(x,v)), (x,v)::applySubToListOfPairs(s2,Substitution(x,v)))
//
    case _ => { println("\n\n\n 8 \n\n\n"); None}
  }



  def getVars(f: FOLExpression): List[FOLVar] = f match {
      case (FOLConst(c)) => Nil
      case (t1 @ FOLVar(x)) => t1.asInstanceOf[FOLVar]::Nil
      case (function @ Function(_, args @ _)) => args.flatMap( a => getVars(a) )
  }



  def appendSubstitutions(sub1: MatchingSubstitution, sub2: MatchingSubstitution) : Option[MatchingSubstitution] =
  {
    for (s <- sub1.map)
      if(sub2.map.contains(s._1) && s._2 != sub2.map.get(s._1))
        return None

    return Some(new MatchingSubstitution(sub1.moduloVarList, sub1.map ++ sub2.map))
  }

  private[fol] class MatchingSubstitution(val moduloVarList: List[Var], m: scala.collection.immutable.Map[Var, LambdaExpression]) extends Substitution(m)
  {
    //override def apply(expression: LambdaExpression): LambdaExpression = applyWithChangeDBIndicesModuloVarList(moduloVarList, expression)
    override protected def applyWithChangeDBIndices(expression: LambdaExpression): LambdaExpression = expression match {
      case x:Var if x.isFree && !moduloVarList.contains(x) => map.get(x) match {
          case Some(t) => t
          case None => x
      }
      case App(m,n) => App(applyWithChangeDBIndices(m), applyWithChangeDBIndices(n))
      case abs: Abs => Abs(abs.variable ,applyWithChangeDBIndices(abs.expressionInScope))
      case _ => expression
    }
  }
  object MatchingSubstitution {
    def apply(moduloVarList: List[Var]): Substitution = new MatchingSubstitution(moduloVarList, new scala.collection.immutable.EmptyMap)
    def apply(moduloVarList: List[Var], v: Var, t: LambdaExpression): Substitution = new MatchingSubstitution(moduloVarList, Substitution(v,t).map)
//    def unapply(moduloVarList: List[Var],  m: scala.collection.immutable.Map[Var, LambdaExpression])
  }

def applySubToListOfPairs(l : List[Tuple2[FOLExpression, FOLExpression]], s : Substitution) : List[Tuple2[FOLExpression, FOLExpression]] = {
  //  l.foldLeft(Nil)((Tuple2(x,v))=> (Tuple2(s.applyFOL(x),s.applyFOL(v))))
  return l.map(a => (s.apply(a._1).asInstanceOf[FOLExpression], s.apply(a._2).asInstanceOf[FOLExpression]))
  }

def createSubstFromListOfPairs(l: List[Tuple2[FOLExpression, FOLExpression]]) : Substitution =
{
  var sub = Substitution()
  for(x <- l)
  {
    sub = sub:::Substitution(x._1.asInstanceOf[FOLVar],x._2)
  }
  return sub
}


  def matchSetOfTuples(moduloVarList: List[Var], s1: List[Tuple2[FOLExpression, FOLExpression]], s2 : List[Tuple2[FOLExpression, FOLExpression]]) : Option[(List[Tuple2[FOLExpression, FOLExpression]], List[Tuple2[FOLExpression, FOLExpression]])] = (s1,s2) match {
    case (((a1,a2)::s), s2) if a1 == a2 => matchSetOfTuples(moduloVarList, s, s2)

    case ((FOLConst (name1),FOLConst (name2))::s,s2) if name1 != name2 => None
    case (((Function(f1,args1), Function(f2, args2)):: (s)), s2)
      if args1.length == args2.length && f1==f2  => {
          return matchSetOfTuples(moduloVarList, args1.zip(args2) ::: s, s2)
      }
    case (((Atom(f1,args1), Atom(f2, args2)):: (s)), s2)
      if args1.length == args2.length && f1==f2  => {
          return matchSetOfTuples(moduloVarList, args1.zip(args2) ::: s, s2)
      }

    case (((x : FOLVar,v)::s), s2) if !getVars(v).contains(x) && !moduloVarList.contains(x) =>
      //  x does not occur in v && x is not in solved form =>
   //   print(applySubToListOfPairs(s,Substitution(x,v)).toString+"\n")
        matchSetOfTuples(moduloVarList, applySubToListOfPairs(s,MatchingSubstitution(moduloVarList,x,v)), (x,v)::applySubToListOfPairs(s2,MatchingSubstitution(moduloVarList,x,v)))


    case (((x : FOLVar,v)::s), s2) if !getVars(v).contains(x) && moduloVarList.contains(x)  =>
      {        
        if(createSubstFromListOfPairs(s2).apply(v) != createSubstFromListOfPairs(s2).map.get(x))
            return None
      //  x does not occur in v && x is not in solved form =>
   //   print(applySubToListOfPairs(s,Substitution(x,v)).toString+"\n")
        return matchSetOfTuples(moduloVarList, s, s2)
      }


    case (((FOLConst (name1), x : FOLVar)::s), s2)  => None

    case (((y: FOLVar, x : FOLVar)::s), s2) if x!=y  => None

    case (Nil, s2) => Some((Nil, s2))
    case _ => None
  }
}
