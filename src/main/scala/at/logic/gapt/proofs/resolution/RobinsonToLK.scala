
package at.logic.gapt.proofs.resolution

import at.logic.gapt.proofs.lkNew._
import at.logic.gapt.proofs._

import scala.collection.mutable

object RobinsonToLK {
  /**
   * Converts a resolution refutation of a sequent into an LK proof.
   *
   * @param resolutionProof  Resolution refutation ending in the empty clause,
   *                         the input clauses are required to be from the CNF of endSequent.
   * @param endSequent  End sequent that resolutionProof refutes.
   * @return LKProof ending in endSequent.
   */
  def apply( resolutionProof: ResolutionProof, endSequent: HOLSequent ): LKProof = {
    assert( resolutionProof.conclusion.isEmpty )
    apply( resolutionProof, endSequent, clause => lkOld2New( PCNF( endSequent, clause ) ) )
  }

  /**
   * Converts a resolution derivation into an LK proof with axioms.
   *
   * @param resolutionDerivation  Resolution derivation.
   * @return  LK proof ending in the conclusion of resolutionDerivation,
   *          where all ArbitraryAxioms occur as InputClauses in resolutionDerivation.
   */
  def apply( resolutionDerivation: ResolutionProof ): LKProof =
    apply( resolutionDerivation, resolutionDerivation.conclusion, ArbitraryAxiom )

  /**
   * Converts a resolution derivation into an LK proof.
   *
   * Input clauses in the resolution derivation are replaced with the LK proofs returned by createAxiom.
   * Their end-sequents are required to be the input clause plus possibly some formulas from endSequent.
   *
   * @param resolutionDerivation  Resolution derivation.
   * @param endSequent  Additional formulas in the end-sequent of the returned LK proof.
   * @param createAxiom  Gives the replacement LK proofs for the input clauses.
   * @return  LK proof ending in endSequent ++ resolutionDerivation.conclusion.
   */
  def apply( resolutionDerivation: ResolutionProof, endSequent: HOLSequent, createAxiom: HOLClause => LKProof ): LKProof = {
    val memo = mutable.Map[ResolutionProof, LKProof]()

    def f( p: ResolutionProof ): LKProof = memo.getOrElseUpdate( p, p match {
      case TautologyClause( atom )   => LogicalAxiom( atom )
      case ReflexivityClause( term ) => ReflexivityAxiom( term )
      case InputClause( cls )        => createAxiom( cls )
      case Factor( p1, idx1 @ Ant( _ ), idx2 ) =>
        ContractionLeftRule( f( p1 ), p1.conclusion( idx1 ) )
      case Factor( p1, idx1 @ Suc( _ ), idx2 ) =>
        ContractionRightRule( f( p1 ), p1.conclusion( idx1 ) )
      case Instance( p1, s ) => applySubstitution( s )( f( p1 ) )
      case Resolution( p1, idx1, p2, idx2 ) =>
        ContractionMacroRule(
          CutRule( f( p1 ), f( p2 ), p1.conclusion( idx1 ) ),
          endSequent ++ p.conclusion, strict = false
        )
      case p @ Paramodulation( p1, eq, p2, lit @ Ant( _ ), poss, dir ) =>
        ContractionMacroRule(
          ParamodulationLeftRule( f( p1 ), p1.conclusion( eq ), f( p2 ), p2.conclusion( lit ), p.rewrittenAtom ),
          endSequent ++ p.conclusion, strict = false
        )
      case p @ Paramodulation( p1, eq, p2, lit @ Suc( _ ), poss, dir ) =>
        ContractionMacroRule(
          ParamodulationRightRule( f( p1 ), p1.conclusion( eq ), f( p2 ), p2.conclusion( lit ), p.rewrittenAtom ),
          endSequent ++ p.conclusion, strict = false
        )
    } )

    WeakeningContractionMacroRule( f( resolutionDerivation ), endSequent )
  }

}
