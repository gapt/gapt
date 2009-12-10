/* Description: A unifier represents a map between variables and terms
**/

package at.logic.unification

import scala.collection.mutable._

import at.logic.language.fol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.hol._
import at.logic.language.hol.propositions._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.logicSymbols._



//trait Unifier extends Map[VariableA[TypeA], TermA[TypeA]]
trait Unifier extends Map[HOLVar, HOLTerm]
class FOLUnifier extends HashMap[HOLVar,HOLTerm] with Unifier

object FOLUnification {
    def unifiy(f:FOLTerm, g:FOLTerm) : Option[Unifier] = {
        var unifier : Unifier = new FOLUnifier();
        None
    }
}