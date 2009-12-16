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
import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.typedLambdaCalculus._

//trait Unifier extends Map[VariableA[TypeA], TermA[TypeA]]
//trait Unifier extends Substitution//Map[Var, LambdaExpression]


trait FOLUnification {
  def unify(f: FOLTerm, g: FOLTerm) : Option[Substitution] = (f,g) match {
    case (FOLConst(x), FOLConst(y)) if x != y => None // symbol clash constants
    case (FOLConst(x), FOLConst(y)) => Some(Substitution(Nil))
    case (Function(x, _), Function(y, _)) if x != y => None // symbol clash functions


    case (t1 @ FOLVar(x), t2 @ FOLConst(c)) => Some(Substitution(SingleSubstitution(t1.asInstanceOf[FOLVar],t2)::Nil))
    case (t3 @ FOLConst(c), t4 @ FOLVar(x)) => unify(t4,t3)


    case (Function(_, args1), Function(_, args2)) if args1.length != args2.length => None // symbol clash functions arity
    case (Function(_, args1), Function(_, args2)) => args1.zip(args2).foldLeft(Some(Substitution(Nil)): Option[Substitution])(func)
    case _ => throw new UnificationException("Unknown terms was given to first order unification: " + f.toString + " - " + g.toString)
  }
  private def func(sigmaOption: Option[Substitution], x: Pair[FOLTerm, FOLTerm]): Option[Substitution] = sigmaOption match {
    case None => None
    case Some(sigma) => unify(sigma(x._1).asInstanceOf[FOLTerm], sigma(x._2).asInstanceOf[FOLTerm]) match {
      case None => None
      case Some(theta) => Some(sigma:::theta)
    }
  }
}