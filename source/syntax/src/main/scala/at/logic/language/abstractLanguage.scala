/**
 * This file represents the whole package of abstract language, it contains the definitions of types, terms and basic values like terms names and symbols
 */

package at.logic.syntax.language

// types of type theory

/**
 * Base class of all type classes
 */
abstract class TypeA
/**
 * Base class of all basics types
 */
abstract class BaseTypeA extends TypeA
/**
 * Base class of all complex types
 */
abstract class ComplexTypeA extends TypeA
/**
 * Implementation of the individual basic type
 */
case class IType() extends BaseTypeA
/**
 * Implementation of the boolean basic type
 */
case class OType() extends BaseTypeA
/**
 * A template for creating arrow types.
 * Remark - Maybe the argument should be sub types?
 * @param left the type which is left to the leftmost arrow
 * @param right the rest of the expression which is right to the leftmost arrow
 */
case class ArrowType(left : TypeA)(right : TypeA) extends ComplexTypeA

/* the symbols of terms. they should be extended in other files (i.e. logical symbols like forall)
*/

/**
 * Base class of all symbols which are used in terms
 */
abstract class SymbolA
/**
 * Implementation represting a term symbol which is a string and contains no internal meaning (unlike equality, etc.)
 * @param name the value of the name
 */
case class Name(name: String) extends SymbolA

/* the abstract term language. represents type theory. the term must be able to create concrete terms by polymorphic methods (like clone) 
*/

/**
 * Base class for all terms. It contains a type as covariant
 * @param sym the head symbol of the term
 */
abstract class TermA[+T <: TypeA](sym: SymbolA) {
  /**
   * Creates an indentical copy of the concrete implementing term
   * @return the copy
   */
  def cloneTerm() : TermA[T]
}
/**
 * Variables are named terms which represent a variable
 * @param name the name
 */
abstract case class VariableA[+T <: TypeA](name: Name ) extends TermA[T](name)
/**
 * GenFunction is a function which can contain symbols other than a Name, such as logical connectives, etc.
 * @param sym the symbol
 * @param params the parameters
 */
abstract case class FunctionA[+T <: TypeA](name: SymbolA, params : List[TermA[TypeA]]) extends TermA[T](name)
/**
 * Constants are functions with empty parameters list
 * @param name the name
 */
abstract case class ConstantA[+T <: TypeA](n: Name ) extends FunctionA[T](n,Nil)





