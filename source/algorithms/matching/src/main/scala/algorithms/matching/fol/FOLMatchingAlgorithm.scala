/*
 * FOLMatchingAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package at.logic.algorithms.matching.fol

import at.logic.algorithms.matching.MatchingAlgorithm
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._
//import at.logic.language.fol.substitutions._
import at.logic.language.fol._

object FOLMatchingAlgorithm extends MatchingAlgorithm[FOLExpression] {
  //def matchTerm(term: LambdaExpression, posInstance: LambdaExpression) = matchTermModulo(term, posInstance, getVars(posInstance.asInstanceOf[FOLExpression]))

  def matchTerm(term1: FOLExpression, term2: FOLExpression, restrictedDomain: List[Var]) = matchSetOfTuples(restrictedDomain, Tuple2(term1,term2)::Nil,Nil) match {
      case Some((Nil,ls)) => Some(Substitution[LambdaExpression](ls.map(x => (x._1.asInstanceOf[FOLVar],x._2))))
      case _ => None
    }
  protected[fol] class MatchingSubstitution(val moduloVarList: List[Var], m: scala.collection.immutable.Map[Var, FOLExpression]) extends Substitution[FOLExpression](m) {
//    override def apply(expression: LambdaExpression): LambdaExpression = applyWithChangeDBIndicesModuloVarList(moduloVarList, expression)
//    protected def applyWithChangeDBIndicesModuloVarList(moduloVarList: List[Var], expression: LambdaExpression): LambdaExpression = expression match {

      override def apply(expression: FOLExpression): FOLExpression = applyWithChangeDBIndices(expression)
      override protected def applyWithChangeDBIndices(expression: FOLExpression): FOLExpression = expression match {
      case x:Var if x.isFree && !moduloVarList.contains(x) => map.get(x) match {
          case Some(t) => t
          case None => x
      }
      case App(m,n) => App(applyWithChangeDBIndices(m.asInstanceOf[FOLExpression]), applyWithChangeDBIndices(n.asInstanceOf[FOLExpression])).asInstanceOf[FOLExpression]
      case abs: Abs => Abs(abs.variable ,applyWithChangeDBIndices(abs.expressionInScope.asInstanceOf[FOLExpression])).asInstanceOf[FOLExpression]
      case _ => { expression }
    }
  }
  object MatchingSubstitution {
    def apply(moduloVarList: List[Var]): Substitution[FOLExpression] = new MatchingSubstitution(moduloVarList, new scala.collection.immutable.EmptyMap)
    def apply(moduloVarList: List[Var], v: Var, t: FOLExpression): Substitution[FOLExpression] = new MatchingSubstitution(moduloVarList, Substitution(v,t).map)
//    def unapply(moduloVarList: List[Var],  m: scala.collection.immutable.Map[Var, LambdaExpression])
  }

def applySubToListOfPairs(l : List[Tuple2[FOLExpression, FOLExpression]], s : Substitution[FOLExpression]) : List[Tuple2[FOLExpression, FOLExpression]] = {
  //  l.foldLeft(Nil)((Tuple2(x,v))=> (Tuple2(s.applyFOL(x),s.applyFOL(v))))
  return l.map(a => (s.apply(a._1), s.apply(a._2)))
  }

def createSubstFromListOfPairs(l: List[Tuple2[FOLExpression, FOLExpression]]) : Substitution[FOLExpression] = {
  var sub = Substitution[FOLExpression]()
  for(x <- l) {
    sub = sub:::Substitution[LambdaExpression](x._1.asInstanceOf[FOLVar],x._2)
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
    case ((Atom(f1,args1), Atom(f2, args2)):: s, s2)
      if args1.length == args2.length && f1==f2  => {
          return matchSetOfTuples(moduloVarList, args1.zip(args2) ::: s, s2)
      }
    case _ => matchSetOfTuples1(moduloVarList, s1, s2)
  }
  def matchSetOfTuples1(moduloVarList: List[Var], s1: List[Tuple2[FOLExpression, FOLExpression]], s2 : List[Tuple2[FOLExpression, FOLExpression]]) : Option[(List[Tuple2[FOLExpression, FOLExpression]], List[Tuple2[FOLExpression, FOLExpression]])] = (s1,s2) match {
    case ((And(left1: FOLFormula, right1: FOLFormula), And(left2: FOLFormula, right2: FOLFormula)) ::s, s2) =>
      {
        return matchSetOfTuples(moduloVarList, (left1, left2) :: (right1, right2) :: s, s2)
      }

    case ((Or(left1: FOLFormula, right1: FOLFormula), Or(left2: FOLFormula, right2: FOLFormula)) ::s, s2) =>
      {
        return matchSetOfTuples(moduloVarList, (left1, left2) :: (right1, right2) :: s, s2)
      }
    case ((Imp(left1: FOLFormula, right1: FOLFormula), Imp(left2: FOLFormula, right2: FOLFormula)) ::s, s2) =>
      {
        return matchSetOfTuples(moduloVarList, (left1, left2) :: (right1, right2) :: s, s2)
      }
    case _ => matchSetOfTuples2(moduloVarList, s1, s2)
  }
  def matchSetOfTuples2(moduloVarList: List[Var], s1: List[Tuple2[FOLExpression, FOLExpression]], s2 : List[Tuple2[FOLExpression, FOLExpression]]) : Option[(List[Tuple2[FOLExpression, FOLExpression]], List[Tuple2[FOLExpression, FOLExpression]])] = (s1,s2) match {
    case ((Neg(sub1: FOLFormula), Neg(sub2: FOLFormula)) ::s, s2) =>
      {
        return matchSetOfTuples(moduloVarList, (sub1, sub2) :: s, s2)
      }

    case ((AllVar(var1: FOLVar, sub1: FOLFormula), AllVar(var2: FOLVar, sub2: FOLFormula)) ::s, s2) =>
      {
        return matchSetOfTuples(var1::var2::moduloVarList, (sub1, sub2) :: s, s2)
      }


    case ((ExVar(var1: FOLVar, sub1: FOLFormula), ExVar(var2: FOLVar, sub2: FOLFormula)) ::s, s2) =>
      {
        return matchSetOfTuples(var1::var2::moduloVarList, (sub1, sub2) :: s, s2)
      }

    case _ => matchSetOfTuples3(moduloVarList, s1, s2)
  }
  def matchSetOfTuples3(moduloVarList: List[Var], s1: List[Tuple2[FOLExpression, FOLExpression]], s2 : List[Tuple2[FOLExpression, FOLExpression]]) : Option[(List[Tuple2[FOLExpression, FOLExpression]], List[Tuple2[FOLExpression, FOLExpression]])] = (s1,s2) match {
    case (((x : FOLVar,v)::s), s2) if !v.getFreeAndBoundVariables._1.toList.contains(x) && !moduloVarList.contains(x) =>
      //  x does not occur in v && x is not in solved form =>
   //   print(applySubToListOfPairs(s,Substitution(x,v)).toString+"\n")
        matchSetOfTuples(moduloVarList, applySubToListOfPairs(s,MatchingSubstitution(moduloVarList,x,v)), (x,v)::applySubToListOfPairs(s2,MatchingSubstitution(moduloVarList,x,v)))


    case (((x : FOLVar,v)::s), s2) if !v.getFreeAndBoundVariables._1.toList.contains(x) && moduloVarList.contains(x)  =>
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
