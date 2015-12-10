package at.logic.gapt

import at.logic.gapt.expr._

package object proofs {

  type FOLSequent = Sequent[FOLFormula]
  val HOLSequent = Sequent
  type HOLSequent = Sequent[HOLFormula]

  implicit class RichFormulaSequent( val sequent: Sequent[HOLFormula] ) {
    def formulas = sequent.elements

    /**
     * Interpretation of the sequent as a formula.
     * Why is this not the definition of a sequent (/\ F -> \/ G)? The current implementation (\/-F \/ G) is
     * only classically equivalent (In IL a -> b :/- -a \/ b).
     */
    def toFormula: HOLFormula = Or( sequent.antecedent.toList.map( f => Neg( f ) ) ++ sequent.succedent )

    def toNegFormula: HOLFormula = And( sequent.antecedent ++ sequent.succedent.map( Neg( _ ) ) )

    def toImplication: HOLFormula = Imp( And( sequent.antecedent.toList ), Or( sequent.succedent ) )
  }

  implicit class RichFOLSequent( sequent: FOLSequent ) {
    def toFormula = Or( sequent.map( -_, identity ).elements )
    def toImplication = And( sequent.antecedent ) --> Or( sequent.succedent )
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
}
