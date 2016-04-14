package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ containsWeakQuantifier, isPrenex, CNFp }
import at.logic.gapt.proofs.{ OccConnector, HOLClause, Sequent }

import scalaz.{ -\/, \/- }

/**
 * Object for calling the `eliminateTheoryAxiom` transformation.
 */
object eliminateTheoryAxioms extends LKVisitor[HOLFormula] {
  /**
   * Eliminates some theory axioms from `proof`, namely those subsumed by `formula`.
   * @param formula A HOLFormula. Must be of the form ∀x,,1,, ... ∀x,,n,, F' with F' quantifier-free.
   * @param proof An LKProof.
   * @return A pair `(proof', conn)` with the following properties: Every theory axiom in `proof` that is subsumed by `formula`
   *         is removed in `proof'` and `formula` may occur in the antecedent of the end sequent of `proof'`; `conn` is an
   *         OccConnector relating `proof` and `proof'`.
   */
  def withOccConnector( formula: HOLFormula )( proof: LKProof ) = recurse( proof, formula )

  /**
   * Eliminates some theory axioms from `proof`, namely those subsumed by `formula`.
   * @param formula A HOLFormula. Must be of the form ∀x,,1,, ... ∀x,,n,, F' with F' quantifier-free.
   * @param proof An LKProof.
   * @return An LKProof `proof'` with the following properties: Every theory axiom in `proof` that is subsumed by `formula`
   *         is removed in `proof'` and `formula` may occur in the antecedent of the end sequent of `proof'`.
   */
  def apply( formula: HOLFormula )( proof: LKProof ) = withOccConnector( formula )( proof )._1

  /**
   *
   * @param proof A theory axiom with sequent A,,1,,,...,A,,k,, :- B,,1,,,...,:B,,n,,.
   * @return If A,,1,,,...,A,,k,, :- B,,1,,,...,:B,,n,, is subsumed by F, returns a proof of
   *         F, A,,1,,,...,A,,k,, :- B,,1,,,...,:B,,n,,. Otherwise the input axiom.
   */
  protected override def visitTheoryAxiom( proof: TheoryAxiom, formula: HOLFormula ) = {
    require( isPrenex( formula ), s"Formula $formula is not prenex." )
    require( !containsWeakQuantifier( formula, true ), s"Formula $formula contains weak quantifiers." )

    val All.Block( vars, matrix ) = formula
    val cnf = CNFp.toClauseList( matrix )
    val cnfFormula = And( cnf map { _.toDisjunction } )
    val TheoryAxiom( sequent ) = proof
    val subs = cnf map {
      clauseSubsumption( _, sequent )
    }
    val maybeSub = subs.find( _.nonEmpty )

    maybeSub match {
      case Some( Some( sub ) ) =>
        val terms = for ( x <- vars ) yield sub.map.getOrElse( x, x )

        val maybeProof = for {
          subroof <- solvePropositional( sub( matrix ) +: sequent )
        } yield ForallLeftBlock( subroof, formula, terms )

        val subProof = maybeProof match {
          case \/-( p )   => p
          case -\/( seq ) => throw new Exception( s"Sequent $seq is not provable." )
        }
        ( subProof, OccConnector.findEquals( subProof.endSequent, sequent ), formula )

      case _ => ( proof, OccConnector( sequent ), formula )
    }
  }
}