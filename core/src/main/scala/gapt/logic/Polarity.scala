package gapt.logic

/**
 * Polarity of a formula.
 *
 * There are two polarities, positive/in-succedent and negative/in-antecedent.  Polarities serve multiple purposes:
 *  - They distinguish strong and weak quantifiers.  A universal (∀) quantifier in positive/in-succedent polarity is
 *    strong (requires an eigenvariable/Skolem inference), and is weak in negative/in-antecedent polarity
 *    (can be instantiated with any term).
 *  - They guide the construction of expansion trees and their deep formulas.  A merge in positive polarity has a
 *    disjunction as deep formula, in negative polarity it has a conjunction.
 *  - They specify the side/cedent of a sequent.
 *
 * Our convention is based on proofs in LK:
 *  - formulas in the succedent are positive
 *  - formulas in the antecedent are negative
 *
 * This is used consistently, except for a major exception: in resolution proofs, the polarity is reversed.  A formula
 * in the antecedent of a clause in a resolution proof has the negative/in-antecedent polarity (as it is in the
 * antecedent of a sequent).  However upon conversion to LK/ET, the polarity switches to positive/in-succedent polarity.
 */
case class Polarity(inSuc: Boolean) extends AnyVal {
  def inAnt = !inSuc

  def positive = inSuc
  def negative = !positive

  def unary_! : Polarity = Polarity(!inSuc)

  override def toString = if (inSuc) "Positive" else "Negative"
}
object Polarity {
  val Positive = Polarity(true)
  val Negative = Polarity(false)

  val InSuccedent = Positive
  val InAntecedent = Negative

  val values = Seq(Negative, Positive)
}
