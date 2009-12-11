/* Description: A unifier represents a map between variables and terms
**/

package at.logic.unification

import scala.collection.mutable._

import at.logic.language.fol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.hol._
import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.typedLambdaCalculus._




//trait Unifier extends Map[VariableA[TypeA], TermA[TypeA]]
trait Unifier extends Substitution//Map[Var, LambdaExpression]
class FOLUnifier extends HashMap[Var,LambdaExpression] with Unifier
/*

trait FOLUnification {
    def unifiy(f:FOLTerm, g:FOLTerm) : Option[Unifier] =
    {
        var unifier : Unifier = new FOLUnifier();
        f match
        {
            case x:Var =>
                    g match
                    {
                        case a:Constant => 
                            {
                                var pair: SingleSubstitution = new SingleSubstitution(x,y)
                                var sub1 = new Substitution(pair)
                                unifier = unifier.applySubstitution(sub1)
                                unifier = unifier:::sub1
                                unifier
                            }
                        case y:Var =>
                            {
                                var pair: SingleSubstitution = new SingleSubstitution(x,y)
                                var sub1 = new Substitution(pair)
                                sub1 = sub1.applySubstitution(unifier)
                                unifier = unifier:::sub1
                                unifier
                            }
                        case y: FOLTerm =>
                            {
                                if(y.getFreeAndBoundVariables._1.contains() || y.getFreeAndBoundVariables._2.contains())
                                  return NULL
                                var pair: SingleSubstitution = new SingleSubstitution(x,y)
                                var sub1 = new Substitution(pair)
                                sub1 = sub1.applySubstitution(unifier)
                                unifier = unifier:::sub1
                                unifier
                            }
                    }

        }

        return unifier
        //None
    }
}*/