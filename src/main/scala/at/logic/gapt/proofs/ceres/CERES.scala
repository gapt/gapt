package at.logic.gapt.proofs.ceres

import at.logic.gapt.proofs.lk.deleteTautologies
import at.logic.gapt.proofs.lkNew._
import at.logic.gapt.proofs.resolution.{ ResolutionProof, RobinsonToLK }
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.expr._

import at.logic.gapt.provers.prover9.Prover9Prover

/**
 * This implementation of the CERES method does the proof reconstruction via Robinson2LK.
 */
object CERES extends CERES
class CERES {
  /**
   * Applies the CERES method to a first order proof with equality. Internally this is handled by the RobinsoToLK method.
   * @param p a first-order LKProof (structural rules, cut, logical rules, equational rules but no definitions, schema,higher order)
   *          also each formula must be a FOLFormula, since the prover9 interface returns proofs from the FOL layer
   * @return an LK Proof in Atomic Cut Normal Form (ACNF) i.e. without quantified cuts
   */
  def apply( p: LKProof ): LKProof = apply( p, x => true )

  /**
   * Applies the CERES method to a first order proof with equality. Internally this is handled by the RobinsoToLK method.
   * @param p a first-order LKProof without strong quantifiers in the end-sequent
   *          (i.e. structural rules, cut, logical rules, equational rules but no definitions, schema,higher order)
   * @param pred a predicate to specify which cut formulas to eliminate
   *             (e.g. x => containsQuantifiers(x) to keep propositional cuts intact)
   * @return an LK Proof in Atomic Cut Normal Form (ACNF) i.e. without quantified cuts
   */
  def apply( p: LKProof, pred: HOLFormula => Boolean ): LKProof = {
    val es = p.endSequent
    val proj = Projections( p, pred ) + CERES.refProjection( es )

    val tapecl = deleteTautologies( CharacteristicClauseSet( StructCreators.extract( p, pred ) ) )
    val prover = new Prover9Prover()

    prover.getRobinsonProof( tapecl ) match {
      case None => throw new Exception( "Prover9 could not refute the characteristic clause set!" )
      case Some( rp ) =>
        apply( es, proj, rp )
    }
  }

  /**
   * Applies the CERES method to a first order proof with equality. Internally this is handled by the RobinsoToLK method.
   * @param endsequent The end-sequent of the original proof
   * @param proj The projections of the original proof
   * @param rp A resolution refutation
   * @return an LK Proof in Atomic Cut Normal Form (ACNF) i.e. without quantified cuts
   */
  def apply( endsequent: HOLSequent, proj: Set[LKProof], rp: ResolutionProof ) = {
    RobinsonToLK( rp, endsequent, fc => CERES.findMatchingProjection( endsequent, proj + CERES.refProjection( endsequent ) )( fc ) )
  }

  def findMatchingProjection( endsequent: HOLSequent, projections: Set[LKProof] )( axfs: HOLSequent ): LKProof = {
    val nLine = sys.props( "line.separator" )
    println( s"end-sequent: $endsequent" )
    println( s"looking for projection to $axfs" )
    projections.find( x => StillmanSubsumptionAlgorithmHOL.subsumes( x.endSequent diff endsequent, axfs ) ) match {
      case None => throw new Exception( "Could not find a projection to " + axfs + " in " +
        projections.map( _.endSequent.diff( endsequent ) ).mkString( "{" + nLine, ";" + nLine, nLine + "}" ) )
      case Some( proj ) =>
        val Some( sub ) = StillmanSubsumptionAlgorithmHOL.subsumes_by( proj.endSequent diff endsequent, axfs )
        val subproj = applySubstitution( sub )( proj )
        require(
          ( subproj.endSequent diff endsequent ).multiSetEquals( axfs ),
          "Instance of projection with end-sequent " + subproj.endSequent + " is not equal to " + axfs + " x " + endsequent
        )
        subproj
    }
  }

  def refProjection( es: HOLSequent ): LKProof = {
    require( es.formulas.nonEmpty, "Can not project reflexivity to an empty end-sequent!" )
    val x = Var( StringSymbol( "x" ), Ti ).asInstanceOf[Var]
    val axiomseq = HOLSequent( Nil, List( Eq( x, x ) ) )
    //addWeakenings(Axiom(axiomseq.antecedent, axiomseq.succedent), axiomseq compose es)
    WeakeningMacroRule( Axiom( axiomseq.antecedent, axiomseq.succedent ), axiomseq compose es )
  }

}
