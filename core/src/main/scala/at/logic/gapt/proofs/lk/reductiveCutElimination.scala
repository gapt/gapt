package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.isAtom
import at.logic.gapt.proofs.lk.ReductiveCutElimination._
import at.logic.gapt.proofs.{ Context, SequentConnector }

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
  def apply( proof: LKProof, cleanStructRules: Boolean = true ) =
    new ReductiveCutElimination().eliminateAllByUppermost( proof, cleanStructRules )

  /**
   * Eliminates free cuts.
   *
   * @param proof The proof subject to free-cut elimination
   * @param cleanStructRules If true the structural rules are cleaned
   * @param ctx Defines constants, inductive types, etc.
   * @return A free-cut free proof.
   */
  def freeCutFree( proof: LKProof, cleanStructRules: Boolean = true )( implicit ctx: Context ) =
    new ReductiveCutElimination().eliminateFreeCuts( proof, cleanStructRules )

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
   * This methods implements a version of Gentzen's cut-elimination
   * proof parameterized by a strategy given by pred_cut and
   * pred_done.
   *
   * The method traverses an LKProof recursively from the bottom
   * up. When it reaches a cut, the method calls pred_cut(global, sub),
   * where global is complete proof under consideration, while sub
   * is the subproof of global ending in the cut. If this call returns
   * true, the cut is reduced using the usual Gentzen cut-elimination
   * rules. If the call returns false, the traversion continues.
   *
   * After every application of a reduction, pred_done(global) is called.
   * If it returns true, the algorithm terminates, returning the current proof.
   * If it returns false, the algorithm continues to traverse the proof.
   *
   * This means that pred_cut and pred_done allow the definition of a (not necessarily
   * terminating!) cut-elimination strategy. A standard implementation (reducing
   * left-uppermost cuts until the proof is cut-free) is provided by another
   * apply method in this class.
   *
   * @param proof The proof to subject to cut-elimination.
   * @param terminateReduction A predicate deciding when to terminate the algorithm.
   * @param reduction  A function defining how cut should be reduced
   * @param cleanStructRules Tells the algorithm whether or not to clean
   * the structural rules. The default value is on, i.e., clean the structural
   * rules
   *
   * @return The proof as it is after pred_done returns true.
   */
  def apply(
    proof:              LKProof,
    terminateReduction: LKProof => Boolean,
    reduction:          LKProof => Option[( LKProof, SequentConnector )],
    cleanStructRules:   Boolean                                          = true
  ): LKProof = {
    steps += proof
    var pr = regularize( proof )
    do {
      val p = recursor( pr, reduction )
      pr = if ( cleanStructRules ) cleanStructuralRules( p ) else p
      if ( recordSteps ) steps += pr
    } while ( !terminateReduction( pr ) )
    if ( !recordSteps ) steps += pr
    pr
  }

  /**
   * Applies a reduction function simultaneously to every lowermost redex in the given proof.
   */
  private object recursor extends LKVisitor[LKProof => Option[( LKProof, SequentConnector )]] {
    override protected def recurse( proof: LKProof, reduction: LKProof => Option[( LKProof, SequentConnector )] ) = {
      reduction( proof ) getOrElse super.recurse( proof, reduction )
    }
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

    def terminateReduction( proof: LKProof ): Boolean = isCutFree( proof )

    this( proof, terminateReduction, reduction, cleanStructRules )
  }

  private def hasRedex[T]( reduction: LKProof => Option[T], proof: LKProof ) =
    proof.subProofs.exists( reduction( _ ).nonEmpty )

  def eliminateInduction( proof: LKProof, cleanStructRules: Boolean = true )( implicit ctx: Context ): LKProof = {
    var newProof = proof
    do {
      newProof = unfoldGroundInductions( newProof, cleanStructRules )
      newProof = freeCutFree( newProof, cleanStructRules )
    } while ( inductionUnfoldingReduction( newProof ).nonEmpty )
    newProof
  }

  /**
   * Unfolds all induction inference with ground induction term in constructor form.
   * @param proof The proof to which this transformation is applied.
   * @param cleanStructRules Indicates whether the structural rules are cleaned during the reduction.
   * @param ctx Defines constants, inductive types, etc.
   * @return A proof of the same end-sequent which contains no induction inference with ground induction term
   *         in constructor form.
   */
  def unfoldGroundInductions( proof: LKProof, cleanStructRules: Boolean = true )( implicit ctx: Context ): LKProof = {

    /**
     * Reduces a given induction inference.
     * @param proof The induction to be reduced
     * @return A proof and a sequent connector obtained by applying an induction unfolding, or None
     *         if the inference rule is not an induction inference with ground induction term in constructor form.
     */
    def reduction( proof: LKProof ): Option[( LKProof, SequentConnector )] = proof match {
      case ind @ InductionRule( _, _, _ ) =>
        inductionUnfoldingReduction.applyWithSequentConnector( ind )
      case _ => None
    }

    /**
     * @return Returns true if and only if there is no more induction inference to be unfolded.
     */
    def terminateReduction( global: LKProof ): Boolean = {
      !global.subProofs.exists( reduction( _ ).nonEmpty )
    }

    this( proof, terminateReduction, reduction, cleanStructRules )
  }

  /**
   * Eliminates free-cuts with respect to induction inferences and equality rules.
   * @param proof The proof to which the transformation is applied.
   * @param cleanStructRules If true structural rules are cleaned during the transformation.
   * @param ctx Defines constants, types, etc.
   * @return A proof which does not contain any free-cuts.
   */
  def eliminateFreeCuts( proof: LKProof, cleanStructRules: Boolean = true )( implicit ctx: Context ): LKProof = {

    /**
     * Reduces a given cut.
     * @param proof The cut be reduced
     * @return A proof obtained by Gentzen's reduction or if the Gentzen reduction
     *         is not applicable to the given proof, then a proof obtained by applying
     *         the induction reduction.
     */
    def reduction( proof: LKProof ): Option[( LKProof, SequentConnector )] = proof match {
      case cut @ CutRule( ind @ InductionRule( _, _, _ ), leftCutFormula, CutRule( _, _, _, _ ), _ ) if ind.mainIndices.head == leftCutFormula && !isGround( ind.term ) => None
      case cut @ CutRule( _, _, _, _ ) if !hasUpperRedex( cut ) =>
        gradeReduction.applyWithSequentConnector( cut )
          .orElse( leftRankReduction.applyWithSequentConnector( cut ) )
          .orElse( rightRankReduction.applyWithSequentConnector( cut ) )
          .orElse( inductionReduction.applyWithSequentConnector( cut ) )
      case _ => None
    }

    /**
     * The subproofs of the given proof not including the proof itself.
     */
    def properSubProofs( proof: LKProof ) = proof.immediateSubProofs.flatMap( _.subProofs )

    /**
     * Returns true if the last inference of the given proof is a redex for the reduction, and false otherwise.
     */
    def isRedex( proof: LKProof ) = reduction( proof ).nonEmpty

    /**
     * Returns true if some inference of this proof which is not the last inference is a redex for the
     * reduction, and false otherwise.
     */
    def hasUpperRedex( proof: LKProof ): Boolean = properSubProofs( proof ).exists( isRedex( _ ) )

    /**
     * @return Returns true if and only if the given proof contains no cut
     *         that is either reducible by Gentzen's method or by induction
     *         reduction.
     */
    def terminateReduction( global: LKProof ): Boolean = {
      !global.subProofs.filter( {
        case CutRule( _, _, _, _ ) => true
        case _: LKProof            => false
      } ).exists( isRedex( _ ) )
    }

    this( proof, terminateReduction, reduction, cleanStructRules )
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

    def terminateReduction( proof: LKProof ): Boolean = isACNF( proof )

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
    this( proof, terminateReduction, reduction, cleanStructRules )
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

    def terminateReduction( proof: LKProof ): Boolean = isACNFTop( proof )

    this( PushWeakeningToLeaves( proof ), terminateReduction, reduction, cleanStructRules )
  }
}

object guessPermutation {
  def apply( oldProof: LKProof, newProof: LKProof ): ( LKProof, SequentConnector ) =
    ( newProof, SequentConnector.guessInjection( newProof.conclusion, oldProof.conclusion ).inv )
}

object gradeReduction {

  def applyWithSequentConnector( cut: CutRule ): Option[( LKProof, SequentConnector )] =
    this( cut ) map { guessPermutation( cut, _ ) }

  /**
   * Reduces the logical complexity of the cut formula or removes the cut.
   *
   * @param cut The proof to which the reduction is applied.
   * @return A reduced proof or None if the reduction could not be applied to the given proof.
   */
  def apply( cut: CutRule ): Option[LKProof] = {
    val CutRule( left, aux1, right, aux2 ) = cut
    ( left, right ) match {
      // If either cut formula is introduced in an axiom, return the other proof.
      case ( LogicalAxiom( _ ), _ ) => Some( right )
      case ( _, LogicalAxiom( _ ) ) => Some( left )

      //FIXME: What do we actually do in case of reflexivity axioms?
      case ( ReflexivityAxiom( s ), TheoryAxiom( sequent ) ) =>
        Some( TheoryAxiom( sequent.delete( aux2 ) ) )

      case ( TopAxiom, WeakeningLeftRule( subProof, Top() ) ) if right.mainIndices.head == aux2 =>
        Some( subProof )

      case ( WeakeningRightRule( subProof, Bottom() ), BottomAxiom ) if left.mainIndices.head == aux1 =>
        Some( subProof )

      // If both cut rules are introduced in theory axiom, replace them by one theory axiom.
      case ( TheoryAxiom( leftSequent ), TheoryAxiom( rightSequent ) ) =>
        Some( TheoryAxiom( leftSequent.delete( aux1 ) ++ rightSequent.delete( aux2 ) ) )

      // If either cut rule is introduced by weakening, delete one subproof and perform lots of weakenings instead.
      case ( l @ WeakeningRightRule( subProof, main ), r ) if l.mainIndices.head == aux1 => // The left cut formula is introduced by weakening
        Some( WeakeningMacroRule( subProof, cut.endSequent ) )

      case ( l, r @ WeakeningLeftRule( subProof, main ) ) if aux2 == right.mainIndices.head => // The right cut formula is introduced by weakening
        Some( WeakeningMacroRule( subProof, cut.endSequent ) )

      // The propositional rules replace the cut with simpler cuts.
      case ( AndRightRule( llSubProof, a1, lrSubProof, a2 ), AndLeftRule( rSubProof, a3, a4 ) ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val tmp = CutRule( lrSubProof, a2, rSubProof, a4 )
        val o = tmp.getRightSequentConnector
        Some( CutRule( llSubProof, a1, tmp, o.child( a3 ) ) )

      case ( OrRightRule( lSubProof, a1, a2 ), OrLeftRule( rlSubProof, a3, rrSubProof, a4 ) ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val tmp = CutRule( lSubProof, a1, rlSubProof, a3 )
        val o = tmp.getLeftSequentConnector
        Some( CutRule( tmp, o.child( a2 ), rrSubProof, a4 ) )

      case ( ImpRightRule( lSubProof, a1, a2 ), ImpLeftRule( rlSubProof, a3, rrSubProof, a4 ) ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val tmp = CutRule( rlSubProof, a3, lSubProof, a1 )
        Some( CutRule( tmp, tmp.getRightSequentConnector.child( a2 ), rrSubProof, a4 ) )

      case ( NegRightRule( lSubProof, a1 ), NegLeftRule( rSubProof, a2 ) ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        Some( CutRule( rSubProof, a2, lSubProof, a1 ) )

      case ( ForallRightRule( lSubProof, a1, eigen, _ ), ForallLeftRule( rSubProof, a2, f, term, _ ) ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val lSubProofNew = Substitution( eigen, term )( lSubProof )
        Some( CutRule( lSubProofNew, rSubProof, right.auxFormulas.head.head ) )

      case ( ExistsRightRule( lSubProof, a2, f, term, _ ), ExistsLeftRule( rSubProof, a1, eigen, _ ) ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val rSubProofNew = Substitution( eigen, term )( rSubProof )
        Some( CutRule( lSubProof, rSubProofNew, left.auxFormulas.head.head ) )

      case ( DefinitionRightRule( lSubProof, a1, definition1 ), DefinitionLeftRule( rSubProof, a2, definition2 ) ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        Some( CutRule( lSubProof, a1, rSubProof, a2 ) )

      // If no grade reduction rule can be applied
      case _ => None
    }
  }
}

object leftRankReduction {

  def applyWithSequentConnector( cut: CutRule ): Option[( LKProof, SequentConnector )] =
    this( cut ) map { guessPermutation( cut, _ ) }

  /**
   * Reduces the rank of the cut by permuting it upwards on the left-hand side.
   *
   * @param cut The proof to which the left rank reduction is applied
   * @return A reduced proof or None if the left rank reduction could not be applied.
   */
  def apply( cut: CutRule ): Option[LKProof] = {
    val CutRule( left, aux1, right, aux2 ) = cut
    left match {
      case l @ WeakeningLeftRule( subProof, main ) =>
        val aux1Sub = l.getSequentConnector.parent( aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        Some( WeakeningLeftRule( cutSub, main ) )

      case l @ WeakeningRightRule( subProof, main ) =>
        Some( WeakeningRightRule( CutRule( subProof, l.getSequentConnector.parent( aux1 ), right, aux2 ), main ) )

      case l @ ContractionLeftRule( subProof, a1, a2 ) =>
        val aux1Sub = l.getSequentConnector.parent( aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val ( a1New, a2New ) = ( cutSub.getLeftSequentConnector.child( a1 ), cutSub.getLeftSequentConnector.child( a2 ) )
        Some( ContractionLeftRule( cutSub, a1New, a2New ) )

      case l @ ContractionRightRule( subProof, a1, a2 ) =>
        if ( l.mainIndices.head == aux1 ) { // The left cut formula is the main formula of the contraction: Duplicate right proof
          val tmp = CutRule( subProof, a1, right, aux2 )
          val tmp2 = CutRule( tmp, tmp.getLeftSequentConnector.child( a2 ), right, aux2 )
          Some(
            regularize(
              ContractionMacroRule( tmp2, left.endSequent.delete( aux1 ) ++ right.endSequent.delete( aux2 ) )
            )
          )
        } else { // The contraction operates on the context: Swap the inferences
          val aux1Sub = l.getSequentConnector.parent( aux1 )
          val cutSub = CutRule( subProof, aux1Sub, right, aux2 )
          val ( a1New, a2New ) = ( cutSub.getLeftSequentConnector.child( a1 ), cutSub.getLeftSequentConnector.child( a2 ) )
          Some( ContractionRightRule( cutSub, a1New, a2New ) )
        }

      //Following line is redundant when eliminating uppermost cut
      case l @ CutRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux1Left = l.getLeftSequentConnector.parents( aux1 )
        val aux1Right = l.getRightSequentConnector.parents( aux1 )
        ( aux1Left, aux1Right ) match {
          case ( Seq( aux1Sub ), Seq() ) => // The left cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( leftSubProof, aux1Sub, right, aux2 )
            Some( CutRule( cutSub, cutSub.getLeftSequentConnector.child( a1 ), rightSubProof, a2 ) )

          case ( Seq(), Seq( aux1Sub ) ) => // The left cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( rightSubProof, aux1Sub, right, aux2 )
            Some( CutRule( leftSubProof, a1, cutSub, cutSub.getLeftSequentConnector.child( a2 ) ) )
        }

      case l @ DefinitionLeftRule( subProof, a, m ) =>
        val aux1Sub = l.getSequentConnector.parent( aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( DefinitionLeftRule( cutSub, aNew, m ) )

      case l @ DefinitionRightRule( subProof, a, m ) if left.mainIndices.head != aux1 =>
        val aux1Sub = l.getSequentConnector.parent( aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( DefinitionRightRule( cutSub, aNew, m ) )

      case l @ AndLeftRule( subProof, a1, a2 ) =>
        val aux1Sub = l.getSequentConnector.parent( aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val ( a1New, a2New ) = ( cutSub.getLeftSequentConnector.child( a1 ), cutSub.getLeftSequentConnector.child( a2 ) )
        Some( AndLeftRule( cutSub, a1New, a2New ) )

      case l @ AndRightRule( leftSubProof, a1, rightSubProof, a2 ) if left.mainIndices.head != aux1 =>
        val aux1Left = l.getLeftSequentConnector.parents( aux1 )
        val aux1Right = l.getRightSequentConnector.parents( aux1 )
        ( aux1Left, aux1Right ) match {
          case ( Seq( aux1Sub ), Seq() ) => // The left cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( leftSubProof, aux1Sub, right, aux2 )
            Some( AndRightRule( cutSub, cutSub.getLeftSequentConnector.child( a1 ), rightSubProof, a2 ) )

          case ( Seq(), Seq( aux1Sub ) ) => // The left cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( rightSubProof, aux1Sub, right, aux2 )
            Some( AndRightRule( leftSubProof, a1, cutSub, cutSub.getLeftSequentConnector.child( a2 ) ) )
        }

      case l @ OrLeftRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux1Left = l.getLeftSequentConnector.parents( aux1 )
        val aux1Right = l.getRightSequentConnector.parents( aux1 )
        ( aux1Left, aux1Right ) match {
          case ( Seq( aux1Sub ), Seq() ) => // The left cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( leftSubProof, aux1Sub, right, aux2 )
            Some( OrLeftRule( cutSub, cutSub.getLeftSequentConnector.child( a1 ), rightSubProof, a2 ) )

          case ( Seq(), Seq( aux1Sub ) ) => // The left cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( rightSubProof, aux1Sub, right, aux2 )
            Some( OrLeftRule( leftSubProof, a1, cutSub, cutSub.getLeftSequentConnector.child( a2 ) ) )
        }

      case l @ OrRightRule( subProof, a1, a2 ) if left.mainIndices.head != aux1 =>
        val aux1Sub = l.getSequentConnector.parent( aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val ( a1New, a2New ) = ( cutSub.getLeftSequentConnector.child( a1 ), cutSub.getLeftSequentConnector.child( a2 ) )
        Some( OrRightRule( cutSub, a1New, a2New ) )

      case l @ ImpLeftRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux1Left = l.getLeftSequentConnector.parents( aux1 )
        val aux1Right = l.getRightSequentConnector.parents( aux1 )
        ( aux1Left, aux1Right ) match {
          case ( Seq( aux1Sub ), Seq() ) => // The left cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( leftSubProof, aux1Sub, right, aux2 )
            Some( ImpLeftRule( cutSub, cutSub.getLeftSequentConnector.child( a1 ), rightSubProof, a2 ) )

          case ( Seq(), Seq( aux1Sub ) ) => // The left cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( rightSubProof, aux1Sub, right, aux2 )
            Some( ImpLeftRule( leftSubProof, a1, cutSub, cutSub.getLeftSequentConnector.child( a2 ) ) )
        }

      case l @ ImpRightRule( subProof, a1, a2 ) if left.mainIndices.head != aux1 =>
        val aux1Sub = l.getSequentConnector.parent( aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val ( a1New, a2New ) = ( cutSub.getLeftSequentConnector.child( a1 ), cutSub.getLeftSequentConnector.child( a2 ) )
        Some( ImpRightRule( cutSub, a1New, a2New ) )

      case l @ NegLeftRule( subProof, a ) =>
        val aux1Sub = l.getSequentConnector.parent( aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( NegLeftRule( cutSub, aNew ) )

      case l @ NegRightRule( subProof, a ) if left.mainIndices.head != aux1 =>
        val aux1Sub = l.getSequentConnector.parent( aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( NegRightRule( cutSub, aNew ) )

      case l @ ForallLeftRule( subProof, a, f, term, quant ) =>
        val aux1Sub = l.getSequentConnector.parent( aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( ForallLeftRule( cutSub, aNew, f, term, quant ) )

      case l @ ForallRightRule( subProof, a, eigen, quant ) if left.mainIndices.head != aux1 =>
        val aux1Sub = l.getSequentConnector.parent( aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( ForallRightRule( cutSub, aNew, eigen, quant ) )

      case l @ ForallSkRightRule( subProof, a, main, skTerm, skDef ) if left.mainIndices.head != aux1 =>
        val aux1Sub = l.getSequentConnector.parent( aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( ForallSkRightRule( cutSub, aNew, main, skTerm, skDef ) )

      case l @ ExistsLeftRule( subProof, a, eigen, quant ) =>
        val aux1Sub = l.getSequentConnector.parent( aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( ExistsLeftRule( cutSub, aNew, eigen, quant ) )

      case l @ ExistsSkLeftRule( subProof, a, main, skTerm, skDef ) =>
        val aux1Sub = l.getSequentConnector.parent( aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( ExistsSkLeftRule( cutSub, aNew, main, skTerm, skDef ) )

      case l @ ExistsRightRule( subProof, a, f, term, quant ) if left.mainIndices.head != aux1 =>
        val aux1Sub = l.getSequentConnector.parent( aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, right, aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( ExistsRightRule( cutSub, aNew, f, term, quant ) )

      case l @ EqualityLeftRule( subProof, eq, aux, indicator ) =>
        val conn1 = l.getSequentConnector
        val cutSub = CutRule( subProof, conn1.parent( aux1 ), right, aux2 )
        val conn2 = cutSub.getLeftSequentConnector
        Some( EqualityLeftRule( cutSub, conn2.child( eq ), conn2.child( aux ), indicator ) )

      case l @ EqualityRightRule( subProof, eq, eaux, indicator ) if l.mainIndices.head != aux1 =>
        val conn1 = l.getSequentConnector
        val cutSub = CutRule( subProof, conn1.parent( aux1 ), right, aux2 )
        val conn2 = cutSub.getLeftSequentConnector
        Some( EqualityRightRule( cutSub, conn2.child( eq ), conn2.child( eaux ), indicator ) )

      // If no rank reduction is possible on the left.
      case _ => None
    }
  }
}

object rightRankReduction {

  def applyWithSequentConnector( cut: CutRule ): Option[( LKProof, SequentConnector )] =
    this( cut ) map { guessPermutation( cut, _ ) }

  /**
   * Reduces the rank of the cut by permuting it upwards on the right-hand side.
   *
   * @param cut The proof to which the right rank reduction is applied
   * @return A reduced proof or None if no right reduction could be applied to the proof.
   */
  def apply( cut: CutRule ): Option[LKProof] = {
    val CutRule( left, aux1, right, aux2 ) = cut
    right match {
      case r @ WeakeningLeftRule( subProof, main ) =>
        if ( aux2 == right.mainIndices.head ) {
          Some( WeakeningMacroRule( subProof, cut.endSequent ) )
        } else {
          Some( WeakeningLeftRule( CutRule( left, aux1, subProof, r.getSequentConnector.parent( aux2 ) ), main ) )
        }

      case r @ WeakeningRightRule( subProof, main ) =>
        val aux2Sub = r.getSequentConnector.parent( aux2 )
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        Some( WeakeningRightRule( cutSub, main ) )

      case r @ ContractionLeftRule( subProof, a1, a2 ) =>
        if ( r.mainIndices.head == aux2 ) {
          // The right cut formula is the main formula of the contraction: Duplicate left proof
          val tmp = CutRule( left, aux1, subProof, a1 )
          val tmp2 = CutRule( left, aux1, tmp, tmp.getRightSequentConnector.child( a2 ) )
          Some( regularize( ContractionMacroRule( tmp2, left.endSequent.delete( aux1 ) ++ right.endSequent.delete( aux2 ) ) ) )
        } else {
          // The contraction operates on the context: Swap the inferences
          val aux2Sub = r.getSequentConnector.parent( aux2 )
          val cutSub = CutRule( left, aux1, subProof, aux2Sub )
          val ( a1New, a2New ) = ( cutSub.getRightSequentConnector.child( a1 ), cutSub.getRightSequentConnector.child( a2 ) )
          Some( ContractionLeftRule( cutSub, a1New, a2New ) )
        }

      case r @ ContractionRightRule( subProof, a1, a2 ) =>
        val aux2Sub = r.getSequentConnector.parent( aux2 )
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val ( a1New, a2New ) = ( cutSub.getRightSequentConnector.child( a1 ), cutSub.getRightSequentConnector.child( a2 ) )
        Some( ContractionRightRule( cutSub, a1New, a2New ) )

      //Following line is redundant when eliminating uppermost cut
      case r @ CutRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux2Left = r.getLeftSequentConnector.parents( aux2 )
        val aux2Right = r.getRightSequentConnector.parents( aux2 )
        ( aux2Left, aux2Right ) match {
          case ( Seq( aux2Sub ), Seq() ) => // The right cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( left, aux1, leftSubProof, aux2Sub )
            Some( CutRule( cutSub, cutSub.getRightSequentConnector.child( a1 ), rightSubProof, a2 ) )
          case ( Seq(), Seq( aux2Sub ) ) => // The right cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( left, aux1, rightSubProof, aux2Sub )
            Some( CutRule( leftSubProof, a1, cutSub, cutSub.getRightSequentConnector.child( a2 ) ) )
        }

      case r @ DefinitionLeftRule( subProof, a, m ) if right.mainIndices.head != aux2 =>
        val aux2Sub = r.getSequentConnector.parent( aux2 )
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( DefinitionLeftRule( cutSub, aNew, m ) )

      case r @ DefinitionRightRule( subProof, a, m ) =>
        val aux2Sub = r.getSequentConnector.parent( aux2 )
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( DefinitionLeftRule( cutSub, aNew, m ) )

      case r @ AndLeftRule( subProof, a1, a2 ) if right.mainIndices.head != aux2 =>
        val aux2Sub = r.getSequentConnector.parent( aux2 )
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val ( a1New, a2New ) = ( cutSub.getRightSequentConnector.child( a1 ), cutSub.getRightSequentConnector.child( a2 ) )
        Some( AndLeftRule( cutSub, a1New, a2New ) )

      case r @ AndRightRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux2Left = r.getLeftSequentConnector.parents( aux2 )
        val aux2Right = r.getRightSequentConnector.parents( aux2 )

        ( aux2Left, aux2Right ) match {
          case ( Seq( aux2Sub ), Seq() ) => // The right cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( left, aux1, leftSubProof, aux2Sub )
            Some( AndRightRule( cutSub, cutSub.getRightSequentConnector.child( a1 ), rightSubProof, a2 ) )

          case ( Seq(), Seq( aux2Sub ) ) => // The right cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( left, aux1, rightSubProof, aux2Sub )
            Some( AndRightRule( leftSubProof, a1, cutSub, cutSub.getRightSequentConnector.child( a2 ) ) )
        }

      case r @ OrLeftRule( leftSubProof, a1, rightSubProof, a2 ) if right.mainIndices.head != aux2 =>
        val aux2Left = r.getLeftSequentConnector.parents( aux2 )
        val aux2Right = r.getRightSequentConnector.parents( aux2 )

        ( aux2Left, aux2Right ) match {
          case ( Seq( aux2Sub ), Seq() ) => // The right cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( left, aux1, leftSubProof, aux2Sub )
            Some( OrLeftRule( cutSub, cutSub.getRightSequentConnector.child( a1 ), rightSubProof, a2 ) )

          case ( Seq(), Seq( aux2Sub ) ) => // The right cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( left, aux1, rightSubProof, aux2Sub )
            Some( OrLeftRule( leftSubProof, a1, cutSub, cutSub.getRightSequentConnector.child( a2 ) ) )
        }

      case r @ OrRightRule( subProof, a1, a2 ) =>
        val aux2Sub = r.getSequentConnector.parent( aux2 )
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val ( a1New, a2New ) = ( cutSub.getRightSequentConnector.child( a1 ), cutSub.getRightSequentConnector.child( a2 ) )
        Some( OrRightRule( cutSub, a1New, a2New ) )

      case r @ ImpLeftRule( leftSubProof, a1, rightSubProof, a2 ) if right.mainIndices.head != aux2 =>
        val aux2Left = r.getLeftSequentConnector.parents( aux2 )
        val aux2Right = r.getRightSequentConnector.parents( aux2 )

        ( aux2Left, aux2Right ) match {
          case ( Seq( aux2Sub ), Seq() ) => // The right cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( left, aux1, leftSubProof, aux2Sub )
            Some( ImpLeftRule( cutSub, cutSub.getRightSequentConnector.child( a1 ), rightSubProof, a2 ) )

          case ( Seq(), Seq( aux2Sub ) ) => // The right cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( left, aux1, rightSubProof, aux2Sub )
            Some( ImpLeftRule( leftSubProof, a1, cutSub, cutSub.getRightSequentConnector.child( a2 ) ) )
        }

      case r @ ImpRightRule( subProof, a1, a2 ) =>
        val aux2Sub = r.getSequentConnector.parent( aux2 )
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val ( a1New, a2New ) = ( cutSub.getRightSequentConnector.child( a1 ), cutSub.getRightSequentConnector.child( a2 ) )
        Some( ImpRightRule( cutSub, a1New, a2New ) )

      case r @ NegLeftRule( subProof, a ) if right.mainIndices.head != aux2 =>
        val aux2Sub = r.getSequentConnector.parent( aux2 )
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( NegLeftRule( cutSub, aNew ) )

      case r @ NegRightRule( subProof, a ) =>
        val aux2Sub = r.getSequentConnector.parent( aux2 )
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( NegRightRule( cutSub, aNew ) )

      case r @ ForallLeftRule( subProof, a, f, term, quant ) if right.mainIndices.head != aux2 =>
        val aux2Sub = r.getSequentConnector.parent( aux2 )
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( ForallLeftRule( cutSub, aNew, f, term, quant ) )

      case r @ ForallRightRule( subProof, a, eigen, quant ) =>
        val aux2Sub = r.getSequentConnector.parent( aux2 )
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( ForallRightRule( cutSub, aNew, eigen, quant ) )

      case r @ ForallSkRightRule( subProof, a, main, skTerm, skDef ) =>
        val aux2Sub = r.getSequentConnector.parent( aux2 )
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( ForallSkRightRule( cutSub, aNew, main, skTerm, skDef ) )

      case r @ ExistsLeftRule( subProof, a, eigen, quant ) if right.mainIndices.head != aux2 =>
        val aux2Sub = r.getSequentConnector.parent( aux2 )
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( ExistsLeftRule( cutSub, aNew, eigen, quant ) )

      case r @ ExistsSkLeftRule( subProof, a, main, skTerm, skDef ) if right.mainIndices.head != aux2 =>
        val aux2Sub = r.getSequentConnector.parent( aux2 )
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( ExistsSkLeftRule( cutSub, aNew, main, skTerm, skDef ) )

      case r @ ExistsRightRule( subProof, a, f, term, quant ) =>
        val aux2Sub = r.getSequentConnector.parent( aux2 )
        val cutSub = CutRule( left, aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( ExistsRightRule( cutSub, aNew, f, term, quant ) )

      case r @ EqualityLeftRule( subProof, eq, eaux, indicator ) if r.mainIndices.head != aux2 && r.eqInConclusion != aux2 =>
        val conn1 = r.getSequentConnector
        val cutSub = CutRule( left, aux1, subProof, conn1.parent( aux2 ) )
        val conn2 = cutSub.getRightSequentConnector
        Some( EqualityLeftRule( cutSub, conn2.child( eq ), conn2.child( eaux ), indicator ) )

      case r @ EqualityRightRule( subProof, eq, eaux, indicator ) if r.eqInConclusion != aux2 =>
        val conn1 = r.getSequentConnector
        val cutSub = CutRule( left, aux1, subProof, conn1.parent( aux2 ) )
        val conn2 = cutSub.getRightSequentConnector
        Some( EqualityRightRule( cutSub, conn2 child eq, conn2 child eaux, indicator ) )

      case _ => None
    }
  }
}

object inductionReduction {

  def applyWithSequentConnector( cut: CutRule )( implicit ctx: Context ): Option[( LKProof, SequentConnector )] =
    this( cut ) map { guessPermutation( cut, _ ) }

  /**
   * Reduces the complexity with respect to cut inferences and induction inferences.
   * @param cut The cut that is to be reduced.
   * @param ctx The context of the proof.
   * @return If the given cut can be reduced w.r.t. some induction rule, then
   *         a proof with a lower complexity is returned. Otherwise None is returned.
   */
  def apply( cut: CutRule )( implicit ctx: Context ): Option[LKProof] = {
    inductionRightReduction( cut ) orElse inductionLeftReduction( cut )
  }
}

object inductionRightReduction {

  def applyWithSequentConnector( cut: CutRule ): Option[( LKProof, SequentConnector )] =
    this( cut ) map { guessPermutation( cut, _ ) }

  /**
   * Reduces the complexity of a cut w.r.t. to an induction inference by
   * moving the cut over the induction inference.
   * @param cut The cut that is to be reduced.
   * @return A reduced proof if the cut is reducible, otherwise None.
   */
  def apply( cut: CutRule ): Option[LKProof] = {
    val CutRule( leftProof, _, rightProof, _ ) = cut
    rightProof match {
      case ind @ InductionRule( _, indFormula, indTerm ) =>
        val targetCase = ind.cases.filter( _.proof.endSequent.antecedent.contains( cut.cutFormula ) ).head
        val newIndCases = ind.cases map {
          indCase =>
            if ( indCase == targetCase ) {
              val subProof = CutRule( leftProof, indCase.proof, cut.cutFormula )
              val hypIndices = indCase.hypotheses.map( subProof.getRightSequentConnector.child( _ ) )
              val conclIndex = subProof.getRightSequentConnector.child( indCase.conclusion )
              InductionCase( subProof, indCase.constructor, hypIndices, indCase.eigenVars, conclIndex )
            } else {
              indCase
            }
        }
        Some( InductionRule( newIndCases, indFormula, indTerm ) )
      case _ => None
    }
  }
}

object inductionUnfoldingReduction {

  /**
   * Tries to apply the reduction.
   *
   * @param induction See [[inductionUnfoldingReduction.apply(induction: InductionRule)]]
   * @param ctx Defines constants, types, etc.
   * @return If the induction rule could be unfolded a proof of the same end-sequent and a sequent connector
   *         is returned, otherwise None is returned.
   */
  def applyWithSequentConnector( induction: InductionRule )( implicit ctx: Context ): Option[( LKProof, SequentConnector )] =
    this( induction ) map { guessPermutation( induction, _ ) }

  /**
   * Tries to apply the induction unfolding reduction to a given inference.
   * @param proof The induction unfolding reduction is tried to applied to the last inference of this proof.
   * @param ctx Defines constants, types, etc.
   * @return None if the proof does not end with an induction inference, otherwise see
   *         [[inductionUnfoldingReduction.apply(induction: InductionRule)]].
   */
  def apply( proof: LKProof )( implicit ctx: Context ): Option[LKProof] = proof match {
    case ind @ InductionRule( _, _, _ ) => apply( ind )
    case _: LKProof                     => None
  }

  /**
   * Tries to unfold an induction inference.
   *
   * @param induction The induction inference to be unfolded.
   * @param ctx Defines constants, types, etc.
   * @return If the given induction's term is ground an in constructor form a proof of the same end-sequent for
   *         which the induction inference has been unfolded is returned, otherwise None.
   */
  def apply( induction: InductionRule )( implicit ctx: Context ): Option[LKProof] =
    if ( isGround( induction.term ) && isConstructorForm( induction.term ) ) {
      Some( unfoldInduction( induction ) )
    } else {
      None
    }
}

object inductionLeftReduction {

  def applyWithSequentConnector( cut: CutRule )( implicit ctx: Context ): Option[( LKProof, SequentConnector )] =
    this( cut ) map { guessPermutation( cut, _ ) }

  /**
   * Reduces a cut by moving the cut towards the proof's leaves.
   * @param cut The cut to be reduced.
   * @param ctx The proof's context.
   * @return A reduced proof if the given cut is reducible w.r.t to some induction inference,
   *         otherwise None.
   */
  def apply( cut: CutRule )( implicit ctx: Context ): Option[LKProof] = {
    val CutRule( leftProof, leftCutFormula, rightProof, _ ) = cut
    leftProof match {
      case ind @ InductionRule( inductionCases, inductionFormula, inductionTerm ) if ind.mainIndices.head != leftCutFormula => {
        val targetCase = inductionCases.filter( _.proof.endSequent.succedent.contains( cut.cutFormula ) ).head
        val newInductionCases = inductionCases map {
          indCase =>
            if ( indCase == targetCase ) {
              val subProof = CutRule( indCase.proof, rightProof, cut.cutFormula )
              val hypIndices = indCase.hypotheses.map( subProof.getLeftSequentConnector.child( _ ) )
              val conclIndex = subProof.getLeftSequentConnector.child( indCase.conclusion )
              InductionCase( subProof, indCase.constructor, hypIndices, indCase.eigenVars, conclIndex )
            } else {
              indCase
            }
        }
        Some( InductionRule( newInductionCases, inductionFormula, inductionTerm ) )
      }
      case _ => None
    }
  }
}

object isConstructorForm {
  /**
   * Checks whether a term is in constructor form.
   * @param term The term that is to be checked.
   * @param ctx The context which defines inductive types, etc.
   * @return true if the term is in constructor form, false otherwise.
   */
  def apply( term: Expr )( implicit ctx: Context ): Boolean = {
    val constructors = ctx.getConstructors( term.ty.asInstanceOf[TBase] ).get
    val Apps( head, arguments ) = term
    constructors.contains( head ) && arguments.filter( _.ty == term.ty ).forall( apply _ )
  }
}

object isGround {
  /**
   * Checks whether an expression is ground.
   * @param expr The expression that is to be checked.
   * @return true if the given expression does not contain any free variables, false otherwise.
   */
  def apply( expr: Expr ): Boolean = freeVariables( expr ).isEmpty
}