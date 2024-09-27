package gapt

import gapt.expr._
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Formula
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLFormula

package object proofs {

  type FOLSequent = Sequent[FOLFormula]
  val HOLSequent = Sequent
  type HOLSequent = Sequent[Formula]

  type Label = String
  type LabelledFormula = (Label, Formula)
  type LabelledSequent = Sequent[LabelledFormula]

  /**
   * Converts a labelled sequent to a sequent.
   *
   * @param sequent The sequent to be converted.
   * @return The sequent obtained from the given sequent by dropping the labels.
   */
  implicit def labelledSequentToSequent(sequent: LabelledSequent): Sequent[Formula] =
    sequent map { _._2 }

  implicit class RichFormulaSequent(private val sequent: HOLSequent) extends AnyVal {
    def formulas = sequent.elements

    def toDisjunction = Or(sequent.map(-_, identity).elements)
    def toConjunction = And(sequent.map(-_, identity).elements)
    def toNegConjunction = And(sequent.map(identity, -_).elements)
    def toImplication = And(sequent.antecedent) --> Or(sequent.succedent)
    def toFormula: Formula = sequent match {
      case Sequent(Seq(), Seq()) => Bottom()
      case Sequent(ant, Seq())   => Neg(And(ant))
      case Sequent(Seq(), suc)   => Or(suc)
      case _                     => sequent.toImplication
    }
  }

  implicit class RichFOLSequent(private val sequent: FOLSequent) extends AnyVal {
    def toDisjunction = (sequent: HOLSequent).toDisjunction.asInstanceOf[FOLFormula]
    def toConjunction = (sequent: HOLSequent).toConjunction.asInstanceOf[FOLFormula]
    def toNegConjunction = (sequent: HOLSequent).toNegConjunction.asInstanceOf[FOLFormula]
    def toImplication = (sequent: HOLSequent).toImplication.asInstanceOf[FOLFormula]
    def toFormula = (sequent: HOLSequent).toFormula.asInstanceOf[FOLFormula]
  }

  val Clause = Sequent
  type Clause[+A] = Sequent[A]

  val HOLClause = Sequent
  type HOLClause = Clause[Atom]
  val FOLClause = Sequent
  type FOLClause = Clause[FOLAtom]

  implicit class RichClause[+A](private val clause: Clause[A]) extends AnyVal {
    def negative = clause.antecedent
    def positive = clause.succedent
  }

  implicit class SeqWrapper[+A](private val s: Seq[A]) extends AnyVal {
    def :-[B >: A](that: Seq[B]): Sequent[B] = Sequent(s, that)
  }

  // The "S" suffixes are necessary to disambiguate from the flatten and flatMap member methods.
  implicit class SequentFlattenOp[A](private val sequentCollection: Iterable[Sequent[A]]) extends AnyVal {
    def flattenS: Sequent[A] = sequentCollection.fold(Sequent())(_ ++ _)
  }
  implicit class SequentFlatMapOp[A](private val collection: Iterable[A]) extends AnyVal {
    def flatMapS[B](f: A => Sequent[B]) = collection.view.map(f).flattenS
  }
}
