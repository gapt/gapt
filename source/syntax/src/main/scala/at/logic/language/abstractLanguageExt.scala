/** 
 * Description: This file defines the logical extensions (like logical operators\equality etc.) to the abstract language
 */

package at.logic.syntax.language.ext

/**
 * Operators extends Symbols and represent a symbol which may have some effect other that just a name
 */
abstract class OperatorA extends SymbolA
/**
 * Forall logical operator
 */
case object ForallOp extends OperatorA
/**
 * And operator
 */
case object AndOp extends OperatorA
/**
 * Or operator
 */
case object OrOp extends OperatorA
/**
 * Not operator
 */
case object NotOp extends OperatorA
