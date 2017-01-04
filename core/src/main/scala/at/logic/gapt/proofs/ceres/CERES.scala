package at.logic.gapt.proofs.ceres

import at.logic.gapt.formats.llk.LLKExporter
import at.logic.gapt.formats.tptp.TPTPFOLExporter
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.resolution._
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.expr._
import at.logic.gapt.provers.ResolutionProver
import at.logic.gapt.provers.escargot.Escargot

/**
 * This implementation of the CERES method does the proof reconstruction via ResolutionToLKProof.
 */
object CERES extends CERES {
  def skipNothing: HOLFormula => Boolean = _ => true

  /**
   * True if the formula is not an equation. Intended use: predicate argument of CERES.
   * In case the only cuts on equations come from a translation of binary equation rules to unary ones,
   * this should provide the same clause sets and projections as the binary rules.
   */
  def skipEquations: HOLFormula => Boolean = { case Eq( _, _ ) => false; case _ => true }

  /**
   * True if the formula is propositional and does not contain free variables other than type i.
   * Intended use: predicate argument of CERES.
   * In case the only cuts on equations come from a translation of binary equation rules to unary ones,
   * this should provide the same clause sets and projections as the binary rules.
   */
  def skipPropositional: HOLFormula => Boolean = {
    case Top()    => false
    case Bottom() => false
    case HOLAtom( HOLAtomConst( _, _ ), args ) =>
      args.flatMap( freeVariables( _ ) ).exists( _.exptype != Ti )
    case Neg( f )    => skipPropositional( f )
    case And( l, r ) => skipPropositional( l ) || skipPropositional( r )
    case Or( l, r )  => skipPropositional( l ) || skipPropositional( r )
    case Imp( l, r ) => skipPropositional( l ) || skipPropositional( r )
    case All( _, _ ) => true
    case Ex( _, _ )  => true
  }

}

class CERES {
  /**
   * Applies the CERES method to a first order proof with equality. Internally this is handled by the RobinsoToLK method.
   *
   * @param p a first-order LKProof (structural rules, cut, logical rules, equational rules but no definitions, schema,higher order)
   *          also each formula must be a FOLFormula, since the prover9 interface returns proofs from the FOL layer
   * @return an LK Proof in Atomic Cut Normal Form (ACNF) i.e. without quantified cuts
   */
  def apply( p: LKProof ): LKProof = apply( p, Escargot )
  def apply( p: LKProof, prover: ResolutionProver ): LKProof = apply( p, CERES.skipNothing, prover )

  /**
   * Applies the CERES method to a first order proof with equality. Internally this is handled by the RobinsoToLK method.
   *
   * @param p a first-order LKProof without strong quantifiers in the end-sequent
   *          (i.e. structural rules, cut, logical rules, equational rules but no definitions, schema,higher order)
   * @param pred a predicate to specify which cut formulas to eliminate
   *             (e.g. x => containsQuantifiers(x) to keep propositional cuts intact)
   * @return an LK Proof where all cuts are quantifier-free
   */
  def apply( p: LKProof, pred: HOLFormula => Boolean ): LKProof = apply( p, pred, Escargot )
  def apply( p: LKProof, pred: HOLFormula => Boolean, prover: ResolutionProver ): LKProof = groundFreeVarsLK.wrap( p ) { p =>
    val es = p.endSequent
    val p_ = regularize( AtomicExpansion( skolemizeInferences( p ) ) )
    val cs = CharacteristicClauseSet( StructCreators.extract( p_, pred ) )
    val proj = Projections( p_, pred )
    val tapecl = subsumedClausesRemoval( deleteTautologies( cs ).toList )

    prover.getResolutionProof( tapecl ) match {
      case None => throw new Exception(
        "The characteristic clause set could not be refuted:\n" +
          TPTPFOLExporter( tapecl )
      )
      case Some( rp ) =>
        cleanStructuralRules( apply( es, proj, eliminateSplitting( rp ) ) )
    }
  }

  /**
   * Applies the CERES method to a first order proof with equality. Internally this is handled by the ResolutionToLKProof method.
   *
   * @param endsequent The end-sequent of the original proof
   * @param projections The projections of the original proof
   * @param rp A resolution refutation
   * @return an LK Proof in Atomic Cut Normal Form (ACNF) i.e. without quantified cuts
   */
  def apply( endsequent: HOLSequent, projections: Set[LKProof], rp: ResolutionProof ) = {
    WeakeningContractionMacroRule(
      ResolutionToLKProof( rp, findMatchingProjection( endsequent, projections ) ),
      endsequent
    )
  }

  /**
   * Finds the matching projection of an input clause in the set of projections.
   * @param endsequent The common end-sequent of all projections.
   * @param projections The set of projections.
   * @param input_clause The clause we need to project to.
   * @return An LK proof endsequent x input_clause contained in projections
   * @note This method is passed to ResolutionToLKProof, which handles the simulation of the reflexivity introduction
   *       rule by itself.
   */
  def findMatchingProjection( endsequent: HOLSequent, projections: Set[LKProof] )( input_clause: Input ): LKProof = {
    val axfs = input_clause.conclusion
    for {
      proj <- projections
      sub <- clauseSubsumption( proj.endSequent diff endsequent, axfs )
    } return WeakeningContractionMacroRule( sub( proj ), endsequent ++ axfs )

    throw new Exception( "Could not find a projection to " + axfs + " in " +
      projections.map( _.endSequent.diff( endsequent ) ).mkString( "{\n", ";\n", "\n}" ) )
  }

}
