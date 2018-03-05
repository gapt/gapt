package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.isAtom
import at.logic.gapt.proofs.lk.ReductiveCutElimination._
import at.logic.gapt.proofs.lk.reductions._
import at.logic.gapt.proofs.{Context, SequentConnector, guessPermutation}

import scala.collection.mutable

/**
 * This object implements a version of Gentzen's cut-elimination
 * proof for our sequent calculus LK. For details, please
 * refer to the documentation of the apply methods.
 */
object ReductiveCutElimination {
  /**
   * This methods implements a version of Gentzen's cut-elimination
   * proof using the (known to be terminating) strategy of reducing
   * a left-uppermost cut. The algorithm terminates when all cuts
   * have been eliminated.
   *
   * @param proof The proof to subject to cut-elimination or restructuring.
   * @param cleanStructRules Tells the algorithm whether or not to clean the structural rules
   * default value is on, i.e. clean the structural rules
   * @return A proof.
   */
  def apply( proof: LKProof, cleanStructRules: Boolean = true ) = {
    require( proof.subProofs.forall {
      case InductionRule( _, _, _ ) => false
      case _                        => true
    }, "Proof contains induction" )
    new ReductiveCutElimination().eliminateAllByUppermost( proof, cleanStructRules )
  }

  def eliminateInduction( proof: LKProof, cleanStructRules: Boolean = true )( implicit ctx: Context ) =
    new ReductiveCutElimination().eliminateInduction( proof, cleanStructRules )

  /**
   * Reduces proof to ACNF using reductive cut elimination
   *
   * @param proof The proof to subject to cut-elimination or restructuring.
   * @param cleanStructRules Tells the algorithm whether or not to clean the structural rules
   * default value is on, i.e. clean the structural rules
   * @return A proof.
   */
  def reduceToACNF( proof: LKProof, cleanStructRules: Boolean = true ) =
    new ReductiveCutElimination().eliminateToACNFByUppermost( proof, cleanStructRules )

  /**
   * Reduces proof to ACNF top using reductive cut elimination
   *
   * @param proof The proof to subject to cut-elimination or restructuring.
   * @param cleanStructRules Tells the algorithm whether or not to clean the structural rules
   * default value is on, i.e. clean the structural rules
   * @return A proof.
   */
  def reduceToACNFTop( proof: LKProof, cleanStructRules: Boolean = true ) =
    new ReductiveCutElimination().eliminateToACNFTopByUppermost( proof, cleanStructRules )

  /**
   * This method checks whether a proof is cut-free.
   * @param proof The proof to check for cut-freeness.
   * @return True if proof does not contain the cut rule, False otherwise.
   */
  def isCutFree( proof: LKProof ): Boolean = proof match {
    case InitialSequent( _ ) => true
    case p: CutRule          => false
    case _                   => proof.immediateSubProofs.forall( isCutFree )
  }

  /**
   * This method checks whether a proof is in ACNF
   *
   * @param proof The proof to check for in ACNF.
   * @return True if proof is in ACNF, False otherwise.
   */
  def isACNF( proof: LKProof ): Boolean = proof match {
    case InitialSequent( _ ) => true
    case CutRule( lsb, l, rsb, r ) =>
      if ( isAtom( lsb.endSequent( l ) ) ) isACNF( lsb ) && isACNF( rsb )
      else false
    case _ => proof.immediateSubProofs.forall( isACNF )
  }
  /**
   * This method checks whether a proof is in ACNF top
   *
   * @param proof The proof to check for in ACNF top.
   * @return True if proof is in ACNF,  False otherwise.
   */
  def isACNFTop( proof: LKProof ): Boolean = proof match {
    case InitialSequent( _ ) => true
    case CutRule( lsb, l, rsb, r ) =>
      if ( isAtom( lsb.endSequent( l ) ) )
        if ( introOrCut( lsb, lsb.endSequent( l ) ) && introOrCut( rsb, rsb.endSequent( r ) ) )
          isACNFTop( lsb ) && isACNFTop( rsb )
        else false
      else false
    case _ => proof.immediateSubProofs.forall( isACNFTop )

  }
  /**
   * Checks if the last rule in proof is a leaf, a cut rule, or a weakening rule on
   * the given formula.
   *
   * @param proof The proof we are checking.
   * @param formula The formula we are checking.
   * @return True is structure is correct or false if not.
   */
  def introOrCut( proof: LKProof, formula: Formula ): Boolean = proof match {
    case LogicalAxiom( _ )             => true
    case CutRule( lsb, l, rsb, r )     => true
    case WeakeningRightRule( _, main ) => if ( main == formula ) true else false
    case WeakeningLeftRule( _, main )  => if ( main == formula ) true else false
    case _                             => false
  }
}

class ReductiveCutElimination {
  val steps = mutable.Buffer[LKProof]()
  var recordSteps: Boolean = false

  /**
   * Transforms a proof by applying a reduction until some specified criterion is satisfied.
   *
   * @param proof The proof to which the transformation is applied.
   * @param reduction A local reduction function.
   * @param cleanStructRules Indicates whether structural rules are cleaned after each step.
   * @return A proof that is obtained from the given proof by applying the reduction function iteratively and
   *         simultaneously to all lowermost redexes of the current proof until the specified criterion is
   *         satisfied.
   */
  def apply(
    proof:            LKProof,
    reduction:        LKProof => Option[( LKProof, SequentConnector )],
    cleanStructRules: Boolean                                          = true ): LKProof = {
    steps += proof
    var pr = proof
    var didReduce = false
    do {
      didReduce = false
      val p = new LKVisitor[Unit] {
        override def recurse( proof: LKProof, u: Unit ): ( LKProof, SequentConnector ) = {
          reduction( proof ) match {
            case Some( ( proof2, conn2 ) ) =>
              didReduce = true
              ( proof2, conn2 )
            case None => super.recurse( proof, u )
          }
        }
      }.apply( pr, () )
      pr = if ( cleanStructRules ) cleanStructuralRules( p ) else p
      if ( recordSteps ) steps += pr
    } while ( didReduce )
    if ( !recordSteps ) steps += pr
    pr
  }

  /**
   * This methods implements a version of Gentzen's cut-elimination
   * proof using the (known to be terminating) strategy of reducing
   * a left-uppermost cut. The algorithm terminates when all cuts
   * have been eliminated.
   *
   * @param proof The proof to subject to cut-elimination.
   * @param cleanStructRules Tells algorithm to clean struct rules or not. Default is on
   *
   * @return The cut-free proof.
   */
  def eliminateAllByUppermost( proof: LKProof, cleanStructRules: Boolean = true ): LKProof = {

    def reduction( proof: LKProof ) = proof match {
      case cut @ CutRule( lsb, _, rsb, _ ) if isCutFree( lsb ) && isCutFree( rsb ) =>
        gradeReduction.applyWithSequentConnector( cut )
          .orElse( leftRankReduction.applyWithSequentConnector( cut ) )
          .orElse( rightRankReduction.applyWithSequentConnector( cut ) )
      case _ => None
    }

    this( proof, reduction, cleanStructRules )
  }

  /**
   * Eliminates inductions from a proof.
   *
   * @param proof The proof to which the transformation is applied.
   * @param cleanStructRules Indicates whether structural rules are cleaned during the reduction.
   * @param ctx Defines constants, types, etc.
   * @return A proof obtained by repeated application of induction unfolding; equality reduction and free-cut
   *         elimination. The reduction ends if there is no more unfoldable induction i.e. there is no induction
   *         inference with constructor form induction term.
   */
  def eliminateInduction( proof: LKProof, cleanStructRules: Boolean = true )( implicit ctx: Context ): LKProof = {
    var newProof = proof
    do {
      newProof = unfoldInductions( newProof, cleanStructRules )
      newProof = pushEqualityInferencesToLeaves( newProof )
      newProof = freeCutElimination( newProof )
    } while ( newProof.subProofs.exists( inductionUnfoldingReduction( _ ).nonEmpty ) )
    newProof
  }

  /**
   * Unfolds all induction inference with induction term in constructor form.
   * @param proof The proof to which this transformation is applied.
   * @param cleanStructRules Indicates whether the structural rules are cleaned during the reduction.
   * @param ctx Defines constants, inductive types, etc.
   * @return A proof of the same end-sequent which contains no induction inference with induction term
   *        in constructor form.
   */
  def unfoldInductions( proof: LKProof, cleanStructRules: Boolean = true )( implicit ctx: Context ): LKProof = {

    /* Reduces a given induction inference.
     * @param proof The induction to be reduced
     * @return A proof and a sequent connector obtained by applying an induction unfolding, or None
     *         if the inference rule is not an induction inference with induction term in constructor form.
     */
    def reduction( proof: LKProof ): Option[( LKProof, SequentConnector )] = proof match {
      case ind @ InductionRule( _, _, _ ) =>
        inductionUnfoldingReduction.applyWithSequentConnector( ind )
      case _ => None
    }

    this( proof, reduction, cleanStructRules )
  }

  /**
   * This algorithm implements a generalization of the Gentzen method which
   * reduces all cuts to atomic cuts.
   *
   * @param proof The proof to subject to cut-elimination.
   * @param cleanStructRules Tells algorithm to clean struct rules or not. Default is on
   *
   * @return The cut-free proof.
   */
  def eliminateToACNFByUppermost( proof: LKProof, cleanStructRules: Boolean = true ): LKProof = {

    def reduction( proof: LKProof ): Option[( LKProof, SequentConnector )] = proof match {
      case cut @ CutRule( lsb, l, rsb, _ ) if !isAtom( lsb.endSequent( l ) ) && isACNF( lsb ) && isACNF( rsb ) =>
        if ( isAtom( lsb.endSequent( l ) ) )
          leftRankReduction.applyWithSequentConnector( cut )
            .orElse( rightRankReduction.applyWithSequentConnector( cut ) )
        else
          gradeReduction.applyWithSequentConnector( cut )
            .orElse( leftRankReduction.applyWithSequentConnector( cut ) )
            .orElse( rightRankReduction.applyWithSequentConnector( cut ) )
      case _ => None
    }
    this( proof, reduction, cleanStructRules )
  }
  /**
   * This algorithm implements a generalization of the Gentzen method which
   * reduces all cuts to atomic cuts and pushes these cuts to the leaves of the proof.
   *
   * @param proof The proof to subject to cut-elimination.
   * @param cleanStructRules Tells algorithm to clean struct rules or not. Default is on
   *
   * @return The cut-free proof.
   */
  def eliminateToACNFTopByUppermost( proof: LKProof, cleanStructRules: Boolean = true ): LKProof = {

    def reduction( proof: LKProof ): Option[( LKProof, SequentConnector )] = proof match {
      case cut @ CutRule( lsb, l, rsb, r ) if isAtom( lsb.endSequent( l ) ) =>
        if ( !( introOrCut( lsb, lsb.endSequent( l ) ) && introOrCut( rsb, rsb.endSequent( r ) ) ) ) {
          if ( introOrCut( lsb, lsb.endSequent( l ) ) )
            rightRankReduction.applyWithSequentConnector( cut )
          else
            leftRankReduction.applyWithSequentConnector( cut )
              .orElse( rightRankReduction.applyWithSequentConnector( cut ) )
        } else {
          None
        }
      case cut @ CutRule( lsb, _, rsb, _ ) if isACNFTop( lsb ) && isACNFTop( rsb ) =>
        gradeReduction.applyWithSequentConnector( cut )
          .orElse( leftRankReduction.applyWithSequentConnector( cut ) )
          .orElse( rightRankReduction.applyWithSequentConnector( cut ) )
      case _ => None
    }

    this( pushAllWeakeningsToLeaves( proof ), reduction, cleanStructRules )
  }
}

//object inductionReduction {
//
//  def applyWithSequentConnector( cut: CutRule )( implicit ctx: Context ): Option[( LKProof, SequentConnector )] =
//    this( cut ) map { guessPermutation( cut, _ ) }
//
//  /**
//   * Reduces the complexity with respect to cut inferences and induction inferences.
//   * @param cut The cut that is to be reduced.
//   * @param ctx The context of the proof.
//   * @return If the given cut can be reduced w.r.t. some induction rule, then
//   *         a proof with a lower complexity is returned. Otherwise None is returned.
//   */
//  def apply( cut: CutRule )( implicit ctx: Context ): Option[LKProof] = {
//    inductionRightReduction( cut ) orElse inductionLeftReduction( cut )
//  }
//}

private object inductionEigenvariables {
  /**
   * Retrieves all of the eigenvariables of a given induction rule.
   * @param induction The induction rule.
   * @return All the eigenvariables of the induction rule.
   */
  def apply( induction: InductionRule ) =
    induction.cases.flatMap( _.eigenVars ).toSet
}

object freeCutElimination {
  /**
   * See [[FreeCutElimination.apply]]
   */
  def apply( proof: LKProof )( implicit ctx: Context ) = {
    ( new FreeCutElimination ).apply( proof )
  }
}

/**
 * Free-cut elimination for proofs with equality and induction.
 * @param ctx Defines constants, types, etc.
 */
class FreeCutElimination( implicit val ctx: Context ) {

  /**
   * Eliminates free-cuts with respect to induction inferences and equality rules.
   * @param proof The proof to which the transformation is applied.
   * @return A proof which does not contain any free-cuts.
   */
  def apply( proof: LKProof ): LKProof = visitor.apply( proof, () )

  private object visitor extends LKVisitor[Unit] {
    override protected def recurse( proof: LKProof, arg: Unit ): ( LKProof, SequentConnector ) = {
      proof match {
        case CutRule( _, _, _, _ ) => {
          val ( tempProof, tempConnector ) = super.recurse( proof, () )
          reduction( tempProof ) match {
            case Some( ( newProof, _ ) ) =>
              ( newProof, SequentConnector.guessInjection(
                fromLower = proof.conclusion, toUpper = newProof.conclusion ).inv )
            case None => ( tempProof, tempConnector )
          }
        }
        case _ => super.recurse( proof, () )
      }
    }

    private def weakeningEqualityOnlyTree( proof: LKProof ) = proof.subProofs.forall {
      case EqualityRightRule( _, _, _, _ ) => true
      case EqualityLeftRule( _, _, _, _ )  => true
      case WeakeningRightRule( _, _ )      => true
      case WeakeningLeftRule( _, _ )       => true
      case InitialSequent( _ )             => true
      case _                               => false
    }

    private def recurseGradeReduction( cut: CutRule ): Option[( LKProof, SequentConnector )] =
      gradeReduction( cut ) map { recurse( _, () ) }

    private def recurseLeftRankReduction( cut: CutRule ): Option[( LKProof, SequentConnector )] =
      leftRankReduction( cut ) map { super.recurse( _, () ) }

    private def recurseRightRankReduction( cut: CutRule ): Option[( LKProof, SequentConnector )] =
      rightRankReduction( cut ) map { super.recurse( _, () ) }

    private def recurseInductionReduction( cut: CutRule ): Option[( LKProof, SequentConnector )] =
      (LeftRankInductionReduction orElse RightRankInductionReduction ).reduce( cut ) map { super.recurse( _, () ) }

    private def reduction( proof: LKProof ): Option[( LKProof, SequentConnector )] = {
      val cut @ CutRule( _, _, _, _ ) = proof
      ( cut.leftSubProof, cut.rightSubProof ) match {
        case ( EqualityLeftRule( _, _, _, _ ), EqualityLeftRule( _, _, _, _ ) )
          | ( EqualityLeftRule( _, _, _, _ ), EqualityRightRule( _, _, _, _ ) )
          | ( EqualityRightRule( _, _, _, _ ), EqualityLeftRule( _, _, _, _ ) )
          | ( EqualityRightRule( _, _, _, _ ), EqualityRightRule( _, _, _, _ )
            ) if weakeningEqualityOnlyTree( cut.leftSubProof ) && weakeningEqualityOnlyTree( cut.rightSubProof ) =>
          recurseGradeReduction( cut )
        case ( EqualityLeftRule( _, _, _, _ ), _ )
          | ( EqualityRightRule( _, _, _, _ ), _ ) if weakeningEqualityOnlyTree( cut.leftSubProof ) =>
          recurseGradeReduction( cut ) orElse recurseRightRankReduction( cut ) orElse recurseInductionReduction( cut )
        case ( _, EqualityLeftRule( _, _, _, _ ) )
          | ( _, EqualityRightRule( _, _, _, _ ) ) if weakeningEqualityOnlyTree( cut.rightSubProof ) =>
          recurseGradeReduction( cut ) orElse recurseLeftRankReduction( cut ) orElse recurseInductionReduction( cut )
        case ( _, _ ) =>
          recurseGradeReduction( cut )
            .orElse( recurseRightRankReduction( cut ) )
            .orElse( recurseLeftRankReduction( cut ) )
            .orElse( recurseInductionReduction( cut ) )
      }
    }
  }
}
