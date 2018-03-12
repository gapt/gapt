package gapt.proofs.lk

import gapt.expr._
import gapt.expr.hol._
import gapt.proofs.{ Context, HOLClause, SequentConnector, Sequent }

/**
 * Given a list of formulas Π, this transforms a proof π of Σ :- Δ into a proof π' of Π, Σ :- Δ.
 *
 * It replaces theory axioms on sequents S that are subsumed by Π with propositional proofs of Π, S.
 */
object makeTheoryAxiomsExplicit extends LKVisitor[Seq[Formula]] {
  /**
   * Eliminates some theory axioms from `proof`, namely those subsumed by `formulas`.
   * @param formulas A list of Formulas. Each must be of the form ∀x,,1,, ... ∀x,,n,, F' with F' quantifier-free.
   * @param proof An LKProof.
   * @return A pair `(proof', conn)` with the following properties: Every theory axiom in `proof` that is subsumed by `formulas`
   *         is removed in `proof'` and elements of `formulas` may occur in the antecedent of the end sequent of `proof'`;
   *        `conn` is an SequentConnector relating `proof` and `proof'`.
   */
  def withSequentConnector( formulas: Formula* )( proof: LKProof ) = recurse( proof, formulas )

  /**
   * Eliminates some theory axioms from `proof`, namely those subsumed by `formulas`.
   * @param formulas A list of Formulas. Each must be of the form ∀x,,1,, ... ∀x,,n,, F' with F' quantifier-free.
   * @param proof An LKProof.
   * @return An LKProof `proof'` with the following properties: Every theory axiom in `proof` that is subsumed by `formulas`
   *         is removed in `proof'` and elements of `formula` may occur in the antecedent of the end sequent of `proof'`.
   */
  def apply( formulas: Formula* )( proof: LKProof ): LKProof = withSequentConnector( formulas: _* )( proof )._1

  def apply( proof: LKProof )( implicit ctx: Context ): LKProof =
    apply( ctx.get[Context.ProofNames].sequents.toSeq map { s => universalClosure( s.toFormula ) }: _* )( proof )

  /**
   *
   * @param proof A theory axiom with sequent A,,1,,,...,A,,k,, :- B,,1,,,...,:B,,n,,.
   * @return If A,,1,,,...,A,,k,, :- B,,1,,,...,:B,,n,, is subsumed by some F in formulas, returns a proof of
   *         F, A,,1,,,...,A,,k,, :- B,,1,,,...,:B,,n,,. Otherwise the input axiom.
   */
  protected override def visitProofLink( proof: ProofLink, formulas: Seq[Formula] ) = {

    val ProofLink( _, sequent ) = proof
    formulas match {
      case Seq() => ( proof, SequentConnector( sequent ) )

      case formula +: rest =>
        require( isPrenex( formula ), s"Formula $formula is not prenex." )
        require( !containsStrongQuantifier( formula, Polarity.InAntecedent ), s"Formula $formula contains strong quantifiers." )
        require( freeVariables( formula ).isEmpty, s"Formula $formula is not fully quantified." )

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
              case Right( p )  => p
              case Left( seq ) => throw new Exception( s"Sequent $seq is not provable." )
            }
            ( subProof, SequentConnector.findEquals( subProof.endSequent, sequent ) )

          case _ => visitProofLink( proof, rest )
        }
    }
  }
  protected override def recurse( proof: LKProof, formulas: Seq[Formula] ) = contractAfter( super.recurse )( proof, formulas )
}