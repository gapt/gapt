package gapt.proofs.ceres

import gapt.formats.llk.LLKExporter
import gapt.formats.tptp.TptpFOLExporter
import gapt.proofs.lk._
import gapt.proofs.resolution._
import gapt.proofs.{ Context, HOLSequent, Sequent }
import gapt.expr._
import gapt.proofs.expansion.{ ExpansionProof, ExpansionSequent }
import gapt.provers.ResolutionProver
import gapt.provers.escargot.Escargot

/**
 * This implementation of the CERES method does the proof reconstruction via ResolutionToLKProof.
 */
object CERES extends CERES {
  def skipNothing: Formula => Boolean = _ => true

  /**
   * True if the formula is not an equation. Intended use: predicate argument of CERES.
   * In case the only cuts on equations come from a translation of binary equation rules to unary ones,
   * this should provide the same clause sets and projections as the binary rules.
   */
  def skipEquations: Formula => Boolean = { case Eq( _, _ ) => false; case _ => true }

  /**
   * True if the formula is propositional and does not contain free variables other than type i.
   * Intended use: predicate argument of CERES.
   * In case the only cuts on equations come from a translation of binary equation rules to unary ones,
   * this should provide the same clause sets and projections as the binary rules.
   */
  def skipPropositional: Formula => Boolean = {
    case Top()    => false
    case Bottom() => false
    case Atom( HOLAtomConst( _, _ ), args ) =>
      args.flatMap( freeVariables( _ ) ).exists( _.ty != Ti )
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
  def apply( p: LKProof, pred: Formula => Boolean ): LKProof = apply( p, pred, Escargot )
  def apply( p: LKProof, pred: Formula => Boolean, prover: ResolutionProver ): LKProof = groundFreeVarsLK.wrap( p ) { p =>
    val es = p.endSequent

    val p_ = regularize( skolemizeLK( AtomicExpansion( p ) ) )
    val cs = CharacteristicClauseSet( StructCreators.extract( p_, pred )( Context() ) )

    val proj = Projections( p_, pred )
    val tapecl = subsumedClausesRemoval( deleteTautologies( cs ).toList )

    prover.getResolutionProof( tapecl ) match {
      case None => throw new Exception(
        "The characteristic clause set could not be refuted:\n" +
          TptpFOLExporter( tapecl ) )
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
      endsequent )
  }

  /**
   * Computes the expansion proof of the CERES-normal form using projections and the resolution refutation.
   *
   * @param p a first-order LKProof without strong quantifiers in the end-sequent
   *          (i.e. structural rules, cut, logical rules, equational rules but no definitions, schema,higher order)
   * @return an expansion proof of the CERES-normal form computed from the projections and the resolution refutation
   */
  @deprecated( "Use CERES.expansionProof instead", since = "2.12" )
  def CERESExpansionProof( p: LKProof, prover: ResolutionProver = Escargot ): ExpansionProof =
    expansionProof( p, prover = prover )

  /**
   * Computes the expansion proof of the CERES-normal form using projections and the resolution refutation.
   *
   * @param p a first-order LKProof without strong quantifiers in the end-sequent
   *          (i.e. structural rules, cut, logical rules, equational rules but no definitions, schema,higher order)
   * @return an expansion proof of the CERES-normal form computed from the projections and the resolution refutation
   */
  def expansionProof( p: LKProof, skip: Formula => Boolean = CERES.skipNothing, prover: ResolutionProver = Escargot ): ExpansionProof = {
    val es = p.endSequent
    val p_ = regularize( AtomicExpansion( skolemizeLK( p ) ) )
    val cs = CharacteristicClauseSet( StructCreators.extract( p_, CERES.skipNothing )( Context() ) )

    val proj = Projections( p_, CERES.skipNothing )
    val tapecl = subsumedClausesRemoval( deleteTautologies( cs ).toList )

    prover.getResolutionProof( tapecl ) match {
      case None => throw new Exception(
        "The characteristic clause set could not be refuted:\n" +
          TptpFOLExporter( tapecl ) )
      case Some( rp ) =>
        ResolutionToExpansionProof( eliminateSplitting( rp ), findPartialExpansionSequent( es, proj ) )
    }
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

  /**
   * Computes the partial expansion sequent of the matching projection of an input clause in the set of projections.
   * @param endsequent The common end-sequent of all projections.
   * @param projections The set of projections.
   * @param input The clause we need to project to, the expansion sequent we want to modify and a set which we do not change.
   * @return An expansion sequent of the projection corresponding to the input clause, without the clause part (we compute
   *         the expansion trees of all formulas in the end-sequent of the projection except of the formulas corresponding
   *         to the input clause).
   */
  def findPartialExpansionSequent( endsequent: HOLSequent, projections: Set[LKProof] )( input: Input, set: Set[( Substitution, ExpansionSequent )] ): ExpansionSequent = {
    var expansionSequent = LKToExpansionProof( findMatchingProjection( endsequent, projections )( input ) ).expansionSequent

    for ( c <- input.sequent.antecedent ) {
      expansionSequent.indicesWhere( _.shallow == c ).find( _.isAnt ) match {
        case None => throw new Exception(
          "Clause not contained in expansion sequent" )
        case Some( index ) =>
          expansionSequent = expansionSequent.delete( index )
      }
    }

    for ( c <- input.sequent.succedent ) {
      expansionSequent.indicesWhere( _.shallow == c ).find( _.isSuc ) match {
        case None => throw new Exception(
          "Clause not contained in expansion sequent" )
        case Some( index ) =>
          expansionSequent = expansionSequent.delete( index )
      }
    }

    var retSeq: ExpansionSequent = Sequent()

    for ( subst <- set.map( _._1 ).seq ) {
      retSeq ++= subst( expansionSequent )
    }

    return retSeq
  }
}
