package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ SequentIndex }
import ReductiveCutElimination._
import at.logic.gapt.expr.hol.isAtom

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
   * @param pred_done A predicate deciding when to terminate the algorithm.
   * @param pred_cut A predicate deciding whether or not to reduce a cut encountered
   * when traversing the proof.
   * @param reduce  A function defining how cut should be reduced
   * @param cleanStructRules Tells the algorithm whether or not to clean
   * the structural rules. The default value is on, i.e., clean the structural
   * rules
   *
   * @return The proof as it is after pred_done returns true.
   */
  def apply( proof: LKProof, pred_done: LKProof => Boolean, pred_cut: ( LKProof, LKProof ) => Boolean,
             reduce: LKProof => LKProof, cleanStructRules: Boolean = true ): LKProof = {
    steps += proof
    // For rank-reduction of strong quantifier inferences, we need to either:
    // 1) rename eigenvariables during rank-reduction, or
    // 2) maintain the invariant that the proof is regular
    // Here, we choose 2).
    var pr = regularize( proof )
    do {
      def pred( local: LKProof ) = pred_cut( pr, local )
      val p = cutElim( pr, reduce )( pred )
      pr = if ( cleanStructRules ) cleanStructuralRules( p ) else p
      if ( recordSteps ) steps += pr
    } while ( !pred_done( pr ) )
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
      case cut @ CutRule( _, _, _, _ ) =>
        cut match {
          case gentzenReduction( reducedProof ) => reducedProof
        }
    }

    def reduceCut( proof: LKProof, cut: LKProof ): Boolean = cut match {
      case CutRule( lsb, _, rsb, _ ) => isCutFree( lsb ) && isCutFree( rsb )
    }

    def terminateReduction( proof: LKProof ): Boolean = isCutFree( proof )

    apply( proof, terminateReduction, reduceCut, reduction, cleanStructRules )
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

    def reduceCut( proof: LKProof, cut: LKProof ): Boolean = cut match {
      case CutRule( lsb, l, rsb, _ ) =>
        !isAtom( lsb.endSequent( l ) ) && isACNF( lsb ) && isACNF( rsb )
    }

    def reduction( proof: LKProof ): LKProof = proof match {
      case cut @ CutRule( lsb, l, _, _ ) =>
        if ( isAtom( lsb.endSequent( l ) ) )
          cut match {
            case leftRankReduction( reducedProof )  => reducedProof
            case rightRankReduction( reducedProof ) => reducedProof
          }
        else
          cut match {
            case gentzenReduction( reducedProof ) => reducedProof
          }
    }

    apply( proof, terminateReduction, reduceCut, reduction, cleanStructRules )
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

    def reduction( proof: LKProof ): LKProof = proof match {
      case cut @ CutRule( lsb, l, _, _ ) =>
        if ( isAtom( lsb.endSequent( l ) ) ) {
          if ( introOrCut( lsb, lsb.endSequent( l ) ) )
            cut match {
              case rightRankReduction( reducedProof ) => reducedProof
            }
          else
            cut match {
              case leftRankReduction( reducedProof )  => reducedProof
              case rightRankReduction( reducedProof ) => reducedProof
            }
        } else
          cut match {
            case gentzenReduction( reducedProof ) => reducedProof
          }
    }

    def terminateReduction( proof: LKProof ): Boolean = isACNFTop( proof )

    def reduceCut( proof: LKProof, cut: LKProof ): Boolean = cut match {
      case CutRule( lsb, l, rsb, r ) =>
        if ( isAtom( lsb.endSequent( l ) ) )
          !( introOrCut( lsb, lsb.endSequent( l ) ) && introOrCut( rsb, rsb.endSequent( r ) ) )
        else isACNFTop( lsb ) && isACNFTop( rsb )
    }

    apply( PushWeakeningToLeaves( proof ), terminateReduction, reduceCut, reduction, cleanStructRules )
  }

  // TODO: Implement this properly, i.e. with SequentIndices.
  /**
   * Recursively traverses a proof until it finds a cut to reduce.
   *
   * @param proof An LKProof.
   * @param pred If true on a cut, reduce this cut.
   * @return A proof with one less cut.
   */
  private def cutElim( proof: LKProof, reduce: LKProof => LKProof )( implicit pred: LKProof => Boolean ): LKProof = proof match {
    case InitialSequent( _ ) => proof

    case WeakeningLeftRule( subProof, formula ) =>
      WeakeningLeftRule( cutElim( subProof, reduce ), formula )

    case WeakeningRightRule( subProof, formula ) =>
      WeakeningRightRule( cutElim( subProof, reduce ), formula )

    case ContractionLeftRule( subProof, _, _ ) =>
      ContractionLeftRule( cutElim( subProof, reduce ), proof.mainFormulas.head )

    case ContractionRightRule( subProof, _, _ ) =>
      ContractionRightRule( cutElim( subProof, reduce ), proof.mainFormulas.head )

    case AndRightRule( leftSubProof, _, rightSubProof, _ ) =>
      AndRightRule( cutElim( leftSubProof, reduce ), cutElim( rightSubProof, reduce ), proof.mainFormulas.head )

    case AndLeftRule( subProof, _, _ ) =>
      AndLeftRule( cutElim( subProof, reduce ), proof.mainFormulas.head )

    case OrLeftRule( leftSubProof, _, rightSubProof, _ ) =>
      OrLeftRule( cutElim( leftSubProof, reduce ), cutElim( rightSubProof, reduce ), proof.mainFormulas.head )

    case OrRightRule( subProof, _, _ ) =>
      OrRightRule( cutElim( subProof, reduce ), proof.mainFormulas.head )

    case ImpLeftRule( leftSubProof, _, rightSubProof, _ ) =>
      ImpLeftRule( cutElim( leftSubProof, reduce ), cutElim( rightSubProof, reduce ), proof.mainFormulas.head )

    case ImpRightRule( subProof, _, _ ) =>
      ImpRightRule( cutElim( subProof, reduce ), proof.mainFormulas.head )

    case NegLeftRule( subProof, _ ) =>
      NegLeftRule( cutElim( subProof, reduce ), proof.auxFormulas.head.head )

    case NegRightRule( subProof, _ ) =>
      NegRightRule( cutElim( subProof, reduce ), proof.auxFormulas.head.head )

    case ForallLeftRule( subProof, _, _, term, _ ) =>
      ForallLeftRule( cutElim( subProof, reduce ), proof.mainFormulas.head, term )

    case ForallRightRule( subProof, _, eigen, _ ) =>
      ForallRightRule( cutElim( subProof, reduce ), proof.mainFormulas.head, eigen )

    case ExistsLeftRule( subProof, _, eigen, _ ) =>
      ExistsLeftRule( cutElim( subProof, reduce ), proof.mainFormulas.head, eigen )

    case ExistsRightRule( subProof, _, _, term, _ ) =>
      ExistsRightRule( cutElim( subProof, reduce ), proof.mainFormulas.head, term )

    case ForallSkRightRule( subProof, _, _, skTerm, skDef ) =>
      ForallSkRightRule( cutElim( subProof, reduce ), skTerm, skDef )

    case ExistsSkLeftRule( subProof, _, _, skTerm, skDef ) =>
      ExistsSkLeftRule( cutElim( subProof, reduce ), skTerm, skDef )

    case EqualityLeftRule( subProof, _, _, _ ) =>
      EqualityLeftRule( cutElim( subProof, reduce ), proof.auxFormulas.head( 0 ), proof.auxFormulas.head( 1 ), proof.mainFormulas.head )

    case EqualityRightRule( subProof, _, _, _ ) =>
      EqualityRightRule( cutElim( subProof, reduce ), proof.auxFormulas.head( 0 ), proof.auxFormulas.head( 1 ), proof.mainFormulas.head )

    case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      if ( pred( proof ) ) reduce( proof )
      else CutRule( cutElim( leftSubProof, reduce ), leftSubProof.endSequent( aux1 ), cutElim( rightSubProof, reduce ), rightSubProof.endSequent( aux2 ) )

  }

  object gentzenReduction {
    /**
     * Reduces a proof by applying either a grade reduction, a left rank reduction
     * or a right rank reduction.
     *
     * @param cut The proof to which the reduction is applied.
     * @return Either a reduced proof or None if the reduction could not be applied.
     */
    def unapply( cut: CutRule ): Option[LKProof] = cut match {
      case gradeReduction( reducedProof )     => Some( reducedProof )
      case leftRankReduction( reducedProof )  => Some( reducedProof )
      case rightRankReduction( reducedProof ) => Some( reducedProof )
    }
  }

  private object gradeReduction {

    /**
     * Reduces the logical complexity of the cut formula or removes the cut.
     *
     * @param cut The proof to which the reduction is applied.
     * @return A reduced proof or None if the reduction could not be applied to the given proof.
     */
    def apply( cut: CutRule ): Option[LKProof] = this.unapply( cut )

    /**
     * See [[gradeReduction.apply( cut: CutRule )]]
     */
    def unapply( cut: CutRule ): Option[LKProof] = {
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
          Some( WeakeningMacroRule( subProof, subProof.endSequent ++ r.endSequent ) )

        case ( l, r @ WeakeningLeftRule( subProof, main ) ) if aux2 == right.mainIndices.head => // The right cut formula is introduced by weakening
          Some( WeakeningMacroRule( subProof, l.endSequent.antecedent, l.endSequent.succedent ) )

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

  private object leftRankReduction {

    /**
     * Reduces the rank of the cut by permuting it upwards on the left-hand side.
     *
     * @param cut The proof to which the left rank reduction is applied
     * @return A reduced proof or None if the left rank reduction could not be applied.
     */
    def apply( cut: CutRule ): Option[LKProof] = this.unapply( cut )

    /**
     * See [[leftRankReduction.apply]]
     */
    def unapply( cut: CutRule ): Option[LKProof] = {
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

        // If no rank reduction is possible on the left.
        case _ => None
      }
    }
  }

  private object rightRankReduction {

    /**
     * Reduces the rank of the cut by permuting it upwards on the right-hand side.
     *
     * @param cut The proof to which the right rank reduction is applied
     * @return A reduced proof or None if no right reduction could be applied to the proof.
     */
    def apply( cut: CutRule ): Option[LKProof] = this.unapply( cut )

    /**
     * See [[rightRankReduction.apply]]
     */
    def unapply( cut: CutRule ): Option[LKProof] = {
      val CutRule( left, aux1, right, aux2 ) = cut
      right match {
        case r @ WeakeningLeftRule( subProof, main ) =>
          if ( aux2 == right.mainIndices.head ) {
            Some( WeakeningMacroRule( subProof, left.endSequent.antecedent, left.endSequent.succedent ) )
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
        case _ => None
      }
    }
  }
}