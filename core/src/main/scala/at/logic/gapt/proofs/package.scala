package at.logic.gapt

import at.logic.gapt.expr._

package object proofs {

  type FOLSequent = Sequent[FOLFormula]
  val HOLSequent = Sequent
  type HOLSequent = Sequent[HOLFormula]

  implicit class RichFormulaSequent( val sequent: HOLSequent ) extends AnyVal {
    def formulas = sequent.elements

    def toDisjunction = Or( sequent.map( -_, identity ).elements )
    def toConjunction = And( sequent.map( -_, identity ).elements )
    def toNegConjunction = And( sequent.map( identity, -_ ).elements )
    def toImplication = And( sequent.antecedent ) --> Or( sequent.succedent )
  }

  implicit class RichFOLSequent( val sequent: FOLSequent ) extends AnyVal {
    def toDisjunction = ( sequent: HOLSequent ).toDisjunction.asInstanceOf[FOLFormula]
    def toConjunction = ( sequent: HOLSequent ).toConjunction.asInstanceOf[FOLFormula]
    def toNegConjunction = ( sequent: HOLSequent ).toNegConjunction.asInstanceOf[FOLFormula]
    def toImplication = ( sequent: HOLSequent ).toImplication.asInstanceOf[FOLFormula]
  }

  val Clause = Sequent
  type Clause[+A] = Sequent[A]

  val HOLClause = Sequent
  type HOLClause = Clause[HOLAtom]
  val FOLClause = Sequent
  type FOLClause = Clause[FOLAtom]

  implicit class RichClause[+A]( val clause: Clause[A] ) {
    def negative = clause.antecedent
    def positive = clause.succedent
  }

  implicit class SeqWrapper[+A]( val s: Seq[A] ) extends AnyVal {
    def :-[B >: A]( that: Seq[B] ): Sequent[B] = Sequent( s, that )
  }
}
