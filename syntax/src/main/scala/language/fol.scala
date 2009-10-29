/**
 * Description: defines the term language of first order logic
 */

package at.logic.syntax.language.fol

import at.logic.syntax.language
import at.logic.syntax.language.ext._

trait FOL[+S <: TypeA, +T <: TermA[S]] extends TermA[S] {
  this: T with FOL[S,T] =>
}

trait FOLTerm[+T <: TermA[IType]] extends FOL[IType,T] {
  this: T with FOLTerm[T] =>
}
trait FOLFormula[+T <: TermA[OType]] extends FOL[OType,T] {
  this: T with FOLFormula[T] =>
}

/**
 * Fol constant
 * @param nm the name
 */
final case class Constant(nm : String) extends ConstantA[IType](Name(nm)) with FOLTerm[Constant] {
  def cloneTerm() = Constant(nm)
}
/**
 * Fol variable
 * @param nm the name
 */
final case class Variable(nm : String) extends VariableA[IType](Name(nm)) with FOLTerm[Variable] {
  def cloneTerm() = Variable(nm)
}

/**
 * Fol function
 * @param nm the name
 */
final case class Function(nm : String, prms : List[FOLTerm[TermA[IType]]]) extends FunctionA[IType](Name(nm), prms) with FOLTerm[Function] {
  def cloneTerm() = Function(nm,prms)
}

/**
 * Fol atom formula
 * @param nm the name
 * @param prms the parameter list
 */
final case class Atom(nm : String, prms : List[FOLTerm[TermA[IType]]]) extends FunctionA[OType](Name(nm), prms) with FOLFormula[Atom] {
  def cloneTerm() = Atom(nm, prms)
}
/**
 * Fol forall formula
 * @param form the nested formula
 */
final case class Forall(form : FOLFormula[TermA[OType]]) extends FunctionA[OType](ForallOp, form::Nil) with FOLFormula[Forall] {
  def cloneTerm() = Forall(form)
}
/**
 * Fol and formula
 * @param form1 the left formula
 * @param form2 the right formula
 */
final case class And(form1 : FOLFormula[TermA[OType]], form2 : FOLFormula[TermA[OType]]) extends FunctionA[OType](AndOp, form1::form2::Nil) with FOLFormula[And] {
  def cloneTerm() = And(form1, form2)
}
/**
 * Fol or formula
 * @param form1 the left formula
 * @param form2 the right formula
 */
final case class Or(form1 : FOLFormula[TermA[OType]], form2 : FOLFormula[TermA[OType]]) extends FunctionA[OType](OrOp, form1::form2::Nil) with FOLFormula[Or] {
  def cloneTerm() = Or(form1, form2)
}
/**
 * Fol or formula
 * @param form1 the left formula
 * @param form2 the right formula
 */
final case class Impl(form1 : FOLFormula[TermA[OType]], form2 : FOLFormula[TermA[OType]]) extends FunctionA[OType](ImplOp, form1::form2::Nil) with FOLFormula[Impl] {
  def cloneTerm() = Impl(form1, form2)
}
/**
 * Fol not formula
 * @param form the negated formula
 */
final case class Not(form : FOLFormula[TermA[OType]]) extends FunctionA[OType](NotOp, form::Nil) with FOLFormula[Not] {
  def cloneTerm() = Not(form)
}
