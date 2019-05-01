package gapt.expr.formula.constants

/**
 * Helper class for logical constants.
 *
 * The logical constans are the propositional connectives, the quantifiers, bottom, top, and the equality constant.
 * A logical constant is different from an expression consisting of only this logical constant, as the expression
 * is an object of type Expr and needs to have a definite type.
 *
 * A logical constant consists of a name (e.g. "∀"), and a set of possible types, (e.g. (Ti->To)->To,
 * ((Ti->Ti)->To)->To, ...).  Subclasses need to implement the function matchType, which matches these possible types.
 * This way we can handle the parametric types of the quantifiers.
 *
 * @param name  The name of this logical constant, e.g. "∀"
 */
abstract class LogicalC( val name: String )
