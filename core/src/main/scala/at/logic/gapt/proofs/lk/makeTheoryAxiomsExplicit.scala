package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.{ CNFp, containsStrongQuantifier, containsWeakQuantifier, isPrenex }
import at.logic.gapt.proofs.{ HOLClause, OccConnector, Sequent }

import scalaz.{ -\/, \/- }

/**
 * Given a list of formulas Π, this transforms a proof π of Σ :- Δ into a proof π' of Π, Σ :- Δ.
 *
 * It replaces theory axioms on sequents S that are subsumed by Π with propositional proofs of Π, S.
 */
object makeTheoryAxiomsExplicit extends LKVisitor[Seq[HOLFormula]] {
  /**
   * Eliminates some theory axioms from `proof`, namely those subsumed by `formulas`.
   * @param formulas A list of HOLFormulas. Each must be of the form ∀x,,1,, ... ∀x,,n,, F' with F' quantifier-free.
   * @param proof An LKProof.
   * @return A pair `(proof', conn)` with the following properties: Every theory axiom in `proof` that is subsumed by `formulas`
   *         is removed in `proof'` and elements of `formulas` may occur in the antecedent of the end sequent of `proof'`;
   *        `conn` is an OccConnector relating `proof` and `proof'`.
   */
  def withOccConnector( formulas: HOLFormula* )( proof: LKProof ) = recurse( proof, formulas )

  /**
   * Eliminates some theory axioms from `proof`, namely those subsumed by `formulas`.
   * @param formulas A list of HOLFormulas. Each must be of the form ∀x,,1,, ... ∀x,,n,, F' with F' quantifier-free.
   * @param proof An LKProof.
   * @return An LKProof `proof'` with the following properties: Every theory axiom in `proof` that is subsumed by `formulas`
   *         is removed in `proof'` and elements of `formula` may occur in the antecedent of the end sequent of `proof'`.
   */
  def apply( formulas: HOLFormula* )( proof: LKProof ) = withOccConnector( formulas: _* )( proof )._1

  /**
   *
   * @param proof A theory axiom with sequent A,,1,,,...,A,,k,, :- B,,1,,,...,:B,,n,,.
   * @return If A,,1,,,...,A,,k,, :- B,,1,,,...,:B,,n,, is subsumed by some F in formulas, returns a proof of
   *         F, A,,1,,,...,A,,k,, :- B,,1,,,...,:B,,n,,. Otherwise the input axiom.
   */
  protected override def visitTheoryAxiom( proof: TheoryAxiom, formulas: Seq[HOLFormula] ) = {

    val TheoryAxiom( sequent ) = proof
    formulas match {
      case Seq() => ( proof, OccConnector( sequent ) )

      case formula +: rest =>
        require( isPrenex( formula ), s"Formula $formula is not prenex." )
        require( !containsStrongQuantifier( formula, Polarity.InAntecedent ), s"Formula $formula contains strong quantifiers." )

        val All.Block( vars, matrix ) = formula
        val cnf = CNFp( matrix )
        val cnfFormula = And( cnf map {
          _.toDisjunction
        } )
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
            ( subProof, OccConnector.findEquals( subProof.endSequent, sequent ) )

          case _ => visitTheoryAxiom( proof, rest )
        }
    }
  }
  protected override def recurse( proof: LKProof, formulas: Seq[HOLFormula] ) = contractAfter( super.recurse )( proof, formulas )
}