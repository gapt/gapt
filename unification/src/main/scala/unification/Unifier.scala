/* Description: A unifier represents a map between variables and terms
**/

package at.logic.unification

import at.logic.syntax.language.{TermA, VariableA, TypeA}

trait Unifier extends Map[VariableA[TypeA], TermA[TypeA]]

