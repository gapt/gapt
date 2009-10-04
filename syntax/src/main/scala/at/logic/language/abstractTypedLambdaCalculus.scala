/*
 * abstractTypedLambdaCalculus.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language


/**
 * Base class of all symbols which are used in terms
 */
abstract class SymbolA


/**
 * Base class of all type classes
 */
abstract class TA
/**
 * Base class of all basics types
 */
abstract class TAtomicA extends TA
/**
 * Base class of all complex types
 */
abstract class TComplexA extends TA
/**
 * Implementation of the individual basic type
 */
case class TInd() extends TAtomicA
/**
 * Implementation of the boolean basic type
 */
case class TBool() extends TAtomicA

/**
 * Implementation of the arrow complex type constructor
 */
case class TArrow[+T1 <: TA, +T2 <: TA]() extends TComplexA


abstract class LambdaExpressionA[+T <: TA]

abstract case class LambdaVarA[+T <: TA](symbol: SymbolA ) extends LambdaExpressionA[T]

abstract case class LambdaAbstractionA[+T1 <: TA, +T2 <: TA](variable: LambdaVarA[T1], expression: LambdaExpressionA[T2] ) extends LambdaExpressionA[TArrow[T1,T2]]

abstract case class LambdaApplicationA[+T1 <: TA, +T2 <: TA](function: LambdaExpressionA[TArrow[T1, T2]], argument: LambdaExpressionA[T1] ) extends LambdaExpressionA[T2]

