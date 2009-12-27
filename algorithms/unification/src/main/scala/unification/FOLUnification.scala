/* Description: A unifier represents a map between variables and terms
**/

package at.logic.unification

import scala.collection.mutable._

import at.logic.language.fol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.substitutions._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.hol._
//import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.typedLambdaCalculus._

//trait Unifier extends Map[VariableA[TypeA], TermA[TypeA]]
//trait Unifier extends Substitution//Map[Var, LambdaExpression]

/*
trait FOLUnification {
  def unify(f: FOLTerm, g: FOLTerm) : Option[Substitution] = (f,g) match {
    case (FOLConst(x), FOLConst(y)) if x != y => None // symbol clash constants
    case (x1 @ FOLVar(x), y1 @ FOLVar(y)) => Some(Substitution(SingleSubstitution(x1.asInstanceOf[FOLVar],y1):: Nil))
    case (FOLConst(x), FOLConst(y)) => Some(Substitution(Nil))
    case (Function(x, _), Function(y, _)) if x != y => None // symbol clash functions


    case (t1 @ FOLVar(x), t2 @ FOLConst(c)) => Some(Substitution(SingleSubstitution(t1.asInstanceOf[FOLVar],t2)::Nil))
    case (t3 @ FOLConst(c), t4 @ FOLVar(x)) => unify(t4,t3)
    case (t31 @ Function(_, _), t41 @ FOLVar(x)) => unify(t41,t31)

    case (FOLConst(_), Function(_, _)) => None
    case (Function(_, _), FOLConst(_)) => None

    case (t5 @ FOLVar(x), t6 @ Function(f, args)) if getVars(t6).contains(t5) => None
    case (t5 @ FOLVar(x), t6 @ Function(f, args)) if !getVars(t6).contains(t5) => Some(Substitution(SingleSubstitution(t5.asInstanceOf[FOLVar],t6)::Nil))


    case (Function(_, args1), Function(_, args2)) if args1.length != args2.length => None // symbol clash functions arity
    case (Function(_, args1), Function(_, args2)) => args1.zip(args2).foldLeft(Some(Substitution(Nil)): Option[Substitution])(func)
    case _ => throw new UnificationException("Unknown terms were given to first order unification: " + f.toString + " - " + g.toString)
  }
  private def func(sigmaOption: Option[Substitution], x: Pair[FOLTerm, FOLTerm]): Option[Substitution] = sigmaOption match {
    case None => None
    case Some(sigma) => unify(sigma(x._1).asInstanceOf[FOLTerm], sigma(x._2).asInstanceOf[FOLTerm]) match {
      case None => None
      //    case Some(theta) => Some(sigma:::theta)
      case Some(theta) => Some(removeRedundanceFromSubst(theta ::: applySub(theta,sigma) ::: applySub(sigma, theta)))
    }
  }
  //returs a list containing all variables in f
  def getVars(f: FOLTerm): List[FOLVar] = f match{
      case (FOLConst(c)) => Nil
      case (t1 @ FOLVar(x)) => t1.asInstanceOf[FOLVar]::Nil   
      case (function @ Function(_, args @ _)) => args.flatMap( a => getVars(a) )
  }
  def printSubst(sub: Substitution) = {
      print("\n\n{")
      for (s <- sub.substitutions) print("<"+s._1.toString1+" , "+s._2.toString1+">; ")
      print("}\n\n")
  }
  
  //applyingSub is applied to sub
  def applySub(sub: Substitution, applyingSub: Substitution): Substitution =
  {
        var newSubstitution: Substitution = new Substitution(Nil)
        for(singleSub <- sub.substitutions)
        {
            var newSubst: Substitution = new Substitution(Nil)
            for(applyingSingleSub <- applyingSub.substitutions)
            {
                if(applyingSingleSub._1 != singleSub._1)
                {
                    newSubst = Substitution(SingleSubstitution(singleSub._1, Substitution(applyingSingleSub::Nil).apply(singleSub._2))::Nil):::newSubst
                }
                else
                {
                    val alg = new FOLUnification{}
                    val s2 = (alg.unify(singleSub._2.asInstanceOf[FOLTerm],applyingSingleSub._2.asInstanceOf[FOLTerm])).get// ::: Substitution(singleSub::Nil)
                    newSubst = Substitution(SingleSubstitution(singleSub._1, s2.apply(singleSub._2))::Nil):::newSubst
                }
            }
            newSubstitution = newSubstitution:::newSubst
        }
        return newSubstitution
  }

    //removes redundnt singleSubstitution from a Substitution
  def removeRedundanceFromSubst(sub: Substitution): Substitution = {
      var newSubst: Substitution = Substitution(Nil)
      var sub1: Substitution = new Substitution(sub.substitutions)
      for(s <- sub.substitutions)
      {
          sub1 = Substitution(sub1.substitutions.tail)
          if(!sub1.substitutions.contains(s))
            newSubst = Substitution(s::Nil) ::: newSubst
      }
      return newSubst
  }

    def isGroundTerm(t: FOLTerm): Boolean = getVars(t).isEmpty
/*
    def removeDuplicationInDomain(sub: Substitution): Substitution = {
        var newSub: Substitution = new Substitution(sub.substitutions)
        for(s <- sub.substitutions)
        {
            var b: Boolean = false
            for(s1 <- sub.substitutions.tail)
            {
                var b: Boolean = false
                if(s._1 == s1._1)
                {
                    if(isGroundTerm(s._1) && !newSub.substitutions.constains(s))
                    {
                        b==true;
                        newSub = Substitution(s::Nil) ::: newSub
                    }
                }
            }
            if(!b)
                newSub = Substitution(s::Nil) ::: newSub
        }
        return newSub
    }*/
}*/