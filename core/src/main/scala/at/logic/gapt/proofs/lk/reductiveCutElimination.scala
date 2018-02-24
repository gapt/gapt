package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.isAtom
import at.logic.gapt.proofs.lk.ReductiveCutElimination._
import at.logic.gapt.proofs.{ Context, SequentConnector, guessPermutation }

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

      case ( TopAxiom, WeakeningLeftRule( subProof, Top() ) ) if right.mainIndices.head == aux2 =>
        Some( subProof )

      case ( WeakeningRightRule( subProof, Bottom() ), BottomAxiom ) if left.mainIndices.head == aux1 =>
        Some( subProof )

      // If either cut rule is introduced by weakening, delete one subproof and perform lots of weakenings instead.
      case ( l @ WeakeningRightRule( subProof, main ), r ) if l.mainIndices.head == aux1 =>
        // The left cut formula is introduced by weakening
        Some( WeakeningMacroRule( subProof, cut.endSequent ) )

      case ( l, r @ WeakeningLeftRule( subProof, main ) ) if aux2 == right.mainIndices.head =>
        // The right cut formula is introduced by weakening
        Some( WeakeningMacroRule( subProof, cut.endSequent ) )

      // The propositional rules replace the cut with simpler cuts.
      case ( AndRightRule( llSubProof, a1, lrSubProof, a2 ), AndLeftRule( rSubProof, a3, a4 )
        ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val tmp = CutRule( lrSubProof, a2, rSubProof, a4 )
        val o = tmp.getRightSequentConnector
        Some( CutRule( llSubProof, a1, tmp, o.child( a3 ) ) )

      case ( OrRightRule( lSubProof, a1, a2 ), OrLeftRule( rlSubProof, a3, rrSubProof, a4 )
        ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val tmp = CutRule( lSubProof, a1, rlSubProof, a3 )
        val o = tmp.getLeftSequentConnector
        Some( CutRule( tmp, o.child( a2 ), rrSubProof, a4 ) )

      case ( ImpRightRule( lSubProof, a1, a2 ), ImpLeftRule( rlSubProof, a3, rrSubProof, a4 )
        ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val tmp = CutRule( rlSubProof, a3, lSubProof, a1 )
        Some( CutRule( tmp, tmp.getRightSequentConnector.child( a2 ), rrSubProof, a4 ) )

      case ( NegRightRule( lSubProof, a1 ), NegLeftRule( rSubProof, a2 )
        ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        Some( CutRule( rSubProof, a2, lSubProof, a1 ) )

      case ( ForallRightRule( lSubProof, a1, eigen, _ ), ForallLeftRule( rSubProof, a2, f, term, _ )
        ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val lSubProofNew = Substitution( eigen, term )( lSubProof )
        Some( CutRule( lSubProofNew, rSubProof, right.auxFormulas.head.head ) )

      case ( ExistsRightRule( lSubProof, a2, f, term, _ ), ExistsLeftRule( rSubProof, a1, eigen, _ )
        ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val rSubProofNew = Substitution( eigen, term )( rSubProof )
        Some( CutRule( lSubProof, rSubProofNew, left.auxFormulas.head.head ) )

      case ( DefinitionRightRule( lSubProof, a1, definition1 ), DefinitionLeftRule( rSubProof, a2, definition2 )
        ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        Some( CutRule( lSubProof, a1, rSubProof, a2 ) )

      case ( eqL @ EqualityRightRule( _, _, _, _ ), eqR @ EqualityLeftRule( _, _, _, _ )
        ) if eqL.mainIndices.head == aux1 && eqR.mainIndices.head == aux2 && eqL.auxFormula == eqR.auxFormula =>
        Some( CutRule( eqL.subProof, eqL.aux, eqR.subProof, eqR.aux ) )

      // If no grade reduction rule can be applied
      case _ => None
    }
  }
}

object LeftRankWeakeningLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ WeakeningLeftRule( subProof, main ) =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        Some( WeakeningLeftRule( cutSub, main ) )
      case _ => None
    }
}

object LeftRankWeakeningRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ WeakeningRightRule( subProof, main ) =>
        Some(
          WeakeningRightRule(
            CutRule(
              subProof, l.getSequentConnector.parent( cut.aux1 ),
              cut.rightSubProof, cut.aux2 ),
            main ) )
      case _ => None
    }
}

object LeftRankContractionLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ ContractionLeftRule( subProof, a1, a2 ) =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val ( a1New, a2New ) = (
          cutSub.getLeftSequentConnector.child( a1 ),
          cutSub.getLeftSequentConnector.child( a2 ) )
        Some( ContractionLeftRule( cutSub, a1New, a2New ) )

      case _ => None
    }
}

object LeftRankContractionRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ ContractionRightRule( subProof, a1, a2 ) =>
        if ( l.mainIndices.head == cut.aux1 ) {
          // The left cut formula is the main formula of the contraction: Duplicate right proof
          val tmp = CutRule( subProof, a1, cut.rightSubProof, cut.aux2 )
          val tmp2 = CutRule( tmp, tmp.getLeftSequentConnector.child( a2 ), cut.rightSubProof, cut.aux2 )
          Some(
            ContractionMacroRule(
              tmp2,
              cut.leftSubProof.endSequent.delete( cut.aux1 ) ++ cut.rightSubProof.endSequent.delete( cut.aux2 ) ) )
        } else { // The contraction operates on the context: Swap the inferences
          val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
          val cutSub = CutRule( subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
          val a1New = cutSub.getLeftSequentConnector.child( a1 )
          val a2New = cutSub.getLeftSequentConnector.child( a2 )
          Some( ContractionRightRule( cutSub, a1New, a2New ) )
        }

      case _ => None
    }
}

object LeftRankCutReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ CutRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux1Left = l.getLeftSequentConnector.parents( cut.aux1 )
        val aux1Right = l.getRightSequentConnector.parents( cut.aux1 )
        ( aux1Left, aux1Right ) match {
          case ( Seq( aux1Sub ), Seq() ) => // The left cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( leftSubProof, aux1Sub, cut.rightSubProof, cut.aux2 )
            Some( CutRule( cutSub, cutSub.getLeftSequentConnector.child( a1 ), rightSubProof, a2 ) )

          case ( Seq(), Seq( aux1Sub ) ) => // The left cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( rightSubProof, aux1Sub, cut.rightSubProof, cut.aux2 )
            Some( CutRule( leftSubProof, a1, cutSub, cutSub.getLeftSequentConnector.child( a2 ) ) )
        }

      case _ => None
    }
}

object LeftRankDefinitionLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ DefinitionLeftRule( subProof, a, m ) =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( DefinitionLeftRule( cutSub, aNew, m ) )

      case _ => None
    }
}

object LeftRankDefinitionRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ DefinitionRightRule( subProof, a, m ) if cut.leftSubProof.mainIndices.head != cut.aux1 =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( DefinitionRightRule( cutSub, aNew, m ) )

      case _ => None
    }
}

object LeftRankAndLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ AndLeftRule( subProof, a1, a2 ) =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val a1New = cutSub.getLeftSequentConnector.child( a1 )
        val a2New = cutSub.getLeftSequentConnector.child( a2 )
        Some( AndLeftRule( cutSub, a1New, a2New ) )

      case _ => None
    }
}
object LeftRankAndRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ AndRightRule( leftSubProof, a1, rightSubProof, a2 ) if cut.leftSubProof.mainIndices.head != cut.aux1 =>
        val aux1Left = l.getLeftSequentConnector.parents( cut.aux1 )
        val aux1Right = l.getRightSequentConnector.parents( cut.aux1 )
        ( aux1Left, aux1Right ) match {
          case ( Seq( aux1Sub ), Seq() ) => // The left cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( leftSubProof, aux1Sub, cut.rightSubProof, cut.aux2 )
            Some( AndRightRule( cutSub, cutSub.getLeftSequentConnector.child( a1 ), rightSubProof, a2 ) )

          case ( Seq(), Seq( aux1Sub ) ) => // The left cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( rightSubProof, aux1Sub, cut.rightSubProof, cut.aux2 )
            Some( AndRightRule( leftSubProof, a1, cutSub, cutSub.getLeftSequentConnector.child( a2 ) ) )
        }

      case _ => None
    }
}

object LeftRankOrLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ OrLeftRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux1Left = l.getLeftSequentConnector.parents( cut.aux1 )
        val aux1Right = l.getRightSequentConnector.parents( cut.aux1 )
        ( aux1Left, aux1Right ) match {
          case ( Seq( aux1Sub ), Seq() ) => // The left cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( leftSubProof, aux1Sub, cut.rightSubProof, cut.aux2 )
            Some( OrLeftRule( cutSub, cutSub.getLeftSequentConnector.child( a1 ), rightSubProof, a2 ) )

          case ( Seq(), Seq( aux1Sub ) ) => // The left cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( rightSubProof, aux1Sub, cut.rightSubProof, cut.aux2 )
            Some( OrLeftRule( leftSubProof, a1, cutSub, cutSub.getLeftSequentConnector.child( a2 ) ) )
        }

      case _ => None
    }
}

object LeftRankOrRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ OrRightRule( subProof, a1, a2 ) if cut.leftSubProof.mainIndices.head != cut.aux1 =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val a1New = cutSub.getLeftSequentConnector.child( a1 )
        val a2New = cutSub.getLeftSequentConnector.child( a2 )
        Some( OrRightRule( cutSub, a1New, a2New ) )

      case _ => None
    }
}

object LeftRankImpLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ ImpLeftRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux1Left = l.getLeftSequentConnector.parents( cut.aux1 )
        val aux1Right = l.getRightSequentConnector.parents( cut.aux1 )
        ( aux1Left, aux1Right ) match {
          case ( Seq( aux1Sub ), Seq() ) => // The left cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( leftSubProof, aux1Sub, cut.rightSubProof, cut.aux2 )
            Some( ImpLeftRule( cutSub, cutSub.getLeftSequentConnector.child( a1 ), rightSubProof, a2 ) )

          case ( Seq(), Seq( aux1Sub ) ) => // The left cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( rightSubProof, aux1Sub, cut.rightSubProof, cut.aux2 )
            Some( ImpLeftRule( leftSubProof, a1, cutSub, cutSub.getLeftSequentConnector.child( a2 ) ) )
        }

      case _ => None
    }
}

object LeftRankImpRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ ImpRightRule( subProof, a1, a2 ) if cut.leftSubProof.mainIndices.head != cut.aux1 =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val a1New = cutSub.getLeftSequentConnector.child( a1 )
        val a2New = cutSub.getLeftSequentConnector.child( a2 )
        Some( ImpRightRule( cutSub, a1New, a2New ) )

      case _ => None
    }
}

object LeftRankNegLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ NegLeftRule( subProof, a ) =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( NegLeftRule( cutSub, aNew ) )

      case _ => None
    }
}

object LeftRankNegRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ NegRightRule( subProof, a ) if cut.leftSubProof.mainIndices.head != cut.aux1 =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( NegRightRule( cutSub, aNew ) )

      case _ => None
    }
}

object LeftRankForallLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ ForallLeftRule( subProof, a, f, term, quant ) =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( ForallLeftRule( cutSub, aNew, f, term, quant ) )

      case _ => None
    }
}

object LeftRankForallRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ ForallRightRule( _, _, _, _
        ) if cut.leftSubProof.mainIndices.head != cut.aux1 && freeVariables( cut.endSequent ).contains( l.eigenVariable ) =>
        val newEigenvariable = rename( l.eigenVariable, freeVariables( cut.endSequent ) )
        val renaming = Substitution( l.eigenVariable -> newEigenvariable )
        val newLeftSubProof = l.copy( subProof = renaming( l.subProof ), eigenVariable = newEigenvariable )
        reduce( cut.copy( leftSubProof = newLeftSubProof ) )

      case left @ ForallRightRule( _, _, _, _ ) if left.mainIndices.head != cut.aux1 =>
        val newSubProof = CutRule(
          left.subProof,
          left.getSequentConnector.parent( cut.aux1 ),
          cut.rightSubProof,
          cut.aux2 )
        Some( left.copy(
          subProof = newSubProof,
          aux = newSubProof.getLeftSequentConnector.child( left.aux ) ) )

      case _ => None
    }
}

object LeftRankForallSkRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ ForallSkRightRule( subProof, a, main, skTerm, skDef ) if cut.leftSubProof.mainIndices.head != cut.aux1 =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( ForallSkRightRule( cutSub, aNew, main, skTerm, skDef ) )

      case _ => None
    }
}

object LeftRankExistsLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case left @ ExistsLeftRule( _, _, _, _ ) if freeVariables( cut.endSequent ).contains( left.eigenVariable ) =>
        val newEigenvariable = rename( left.eigenVariable, freeVariables( cut.endSequent ) )
        val renaming = Substitution( left.eigenVariable -> newEigenvariable )
        val newLeftSubProof = left.copy( subProof = renaming( left.subProof ), eigenVariable = newEigenvariable )
        reduce( cut.copy( leftSubProof = newLeftSubProof ) )

      case left @ ExistsLeftRule( _, _, _, _ ) =>
        val newSubProof = CutRule(
          left.subProof,
          left.getSequentConnector.parent( cut.aux1 ),
          cut.rightSubProof,
          cut.aux2 )
        Some( left.copy(
          subProof = newSubProof,
          aux = newSubProof.getLeftSequentConnector.child( left.aux ) ) )
      case _ => None
    }
}

object LeftRankExistsSkLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ ExistsSkLeftRule( subProof, a, main, skTerm, skDef ) =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( ExistsSkLeftRule( cutSub, aNew, main, skTerm, skDef ) )

      case _ => None
    }
}

object LeftRankExistsRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ ExistsRightRule( subProof, a, f, term, quant ) if cut.leftSubProof.mainIndices.head != cut.aux1 =>
        val aux1Sub = l.getSequentConnector.parent( cut.aux1 )
        val cutSub = CutRule( l.subProof, aux1Sub, cut.rightSubProof, cut.aux2 )
        val aNew = cutSub.getLeftSequentConnector.child( a )
        Some( ExistsRightRule( cutSub, aNew, f, term, quant ) )

      case _ => None
    }
}

object LeftRankEqualityLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ EqualityLeftRule( subProof, eq, aux, indicator ) =>
        val conn1 = l.getSequentConnector
        val cutSub = CutRule( subProof, conn1.parent( cut.aux1 ), cut.rightSubProof, cut.aux2 )
        val conn2 = cutSub.getLeftSequentConnector
        Some( EqualityLeftRule( cutSub, conn2.child( eq ), conn2.child( aux ), indicator ) )

      case _ => None
    }
}

object LeftRankEqualityRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] =
    cut.leftSubProof match {
      case l @ EqualityRightRule( subProof, eq, eaux, indicator ) if l.mainIndices.head != cut.aux1 =>
        val conn1 = l.getSequentConnector
        val cutSub = CutRule( subProof, conn1.parent( cut.aux1 ), cut.rightSubProof, cut.aux2 )
        val conn2 = cutSub.getLeftSequentConnector
        Some( EqualityRightRule( cutSub, conn2.child( eq ), conn2.child( eaux ), indicator ) )
      case _ => None
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
  def apply( cut: CutRule ): Option[LKProof] =
    LeftRankWeakeningLeftReduction.reduce( cut ) orElse
      LeftRankWeakeningRightReduction.reduce( cut ) orElse
      LeftRankContractionLeftReduction.reduce( cut ) orElse
      LeftRankContractionRightReduction.reduce( cut ) orElse
      LeftRankCutReduction.reduce( cut ) orElse
      LeftRankDefinitionLeftReduction.reduce( cut ) orElse
      LeftRankDefinitionRightReduction.reduce( cut ) orElse
      LeftRankAndLeftReduction.reduce( cut ) orElse
      LeftRankAndRightReduction.reduce( cut ) orElse
      LeftRankOrLeftReduction.reduce( cut ) orElse
      LeftRankOrRightReduction.reduce( cut ) orElse
      LeftRankImpLeftReduction.reduce( cut ) orElse
      LeftRankImpRightReduction.reduce( cut ) orElse
      LeftRankNegLeftReduction.reduce( cut ) orElse
      LeftRankNegRightReduction.reduce( cut ) orElse
      LeftRankForallLeftReduction.reduce( cut ) orElse
      LeftRankForallRightReduction.reduce( cut ) orElse
      LeftRankForallSkRightReduction.reduce( cut ) orElse
      LeftRankExistsLeftReduction.reduce( cut ) orElse
      LeftRankExistsSkLeftReduction.reduce( cut ) orElse
      LeftRankExistsRightReduction.reduce( cut ) orElse
      LeftRankEqualityLeftReduction.reduce( cut ) orElse
      LeftRankEqualityRightReduction.reduce( cut )
}

trait Reduction {
  def reduce( proof: LKProof ): Option[LKProof]
}

trait CutReduction extends Reduction {
  def reduce( proof: LKProof ): Option[LKProof] =
    proof match {
      case cut @ CutRule( _, _, _, _ ) => reduce( cut )
      case _                           => None
    }
  def reduce( proof: CutRule ): Option[LKProof]
}

object RightRankWeakeningRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case weakening @ WeakeningRightRule( _, _ ) =>
        val aux2Sub = weakening.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, weakening.subProof, aux2Sub )
        Some( WeakeningRightRule( cutSub, weakening.mainFormula ) )
      case _ => None
    }
}

object RightRankWeakeningLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case weakening @ WeakeningLeftRule( _, _ ) =>
        if ( cut.aux2 == cut.rightSubProof.mainIndices.head ) {
          Some( WeakeningMacroRule( weakening.subProof, cut.endSequent ) )
        } else {
          Some(
            WeakeningLeftRule(
              CutRule(
                cut.leftSubProof,
                cut.aux1,
                weakening.subProof,
                weakening.getSequentConnector.parent( cut.aux2 ) ),
              weakening.mainFormula ) )
        }
      case _ => None
    }
}

object RightRankContractionLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ ContractionLeftRule( subProof, a1, a2 ) =>
        if ( r.mainIndices.head == cut.aux2 ) {
          // The right cut formula is the main formula of the contraction: Duplicate left proof
          val tmp = CutRule( cut.leftSubProof, cut.aux1, subProof, a1 )
          val tmp2 = CutRule( cut.leftSubProof, cut.aux1, tmp, tmp.getRightSequentConnector.child( a2 ) )
          Some(
            ContractionMacroRule(
              tmp2,
              cut.leftSubProof.endSequent.delete( cut.aux1 ) ++ cut.rightSubProof.endSequent.delete( cut.aux2 ) ) )
        } else {
          // The contraction operates on the context: Swap the inferences
          val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
          val cutSub = CutRule( cut.leftSubProof, cut.aux1, subProof, aux2Sub )
          val a1New = cutSub.getRightSequentConnector.child( a1 )
          val a2New = cutSub.getRightSequentConnector.child( a2 )
          Some( ContractionLeftRule( cutSub, a1New, a2New ) )
        }
      case _ => None
    }
}

object RightRankContractionRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ ContractionRightRule( subProof, a1, a2 ) =>
        val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, r.subProof, aux2Sub )
        val a1New = cutSub.getRightSequentConnector.child( a1 )
        val a2New = cutSub.getRightSequentConnector.child( a2 )
        Some( ContractionRightRule( cutSub, a1New, a2New ) )

      case _ => None
    }
}

object RightRankCutReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case upperCut @ CutRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux2Left = upperCut.getLeftSequentConnector.parents( cut.aux2 )
        val aux2Right = upperCut.getRightSequentConnector.parents( cut.aux2 )
        ( aux2Left, aux2Right ) match {
          case ( Seq( aux2Sub ), Seq() ) => // The right cut formula is in the left subproof of the binary inference
            val cutSub = CutRule( cut.leftSubProof, cut.aux1, leftSubProof, aux2Sub )
            Some( CutRule( cutSub, cutSub.getRightSequentConnector.child( a1 ), rightSubProof, a2 ) )
          case ( Seq(), Seq( aux2Sub ) ) => // The right cut formula is in the right subproof of the binary inference
            val cutSub = CutRule( cut.leftSubProof, cut.aux1, rightSubProof, aux2Sub )
            Some( CutRule( leftSubProof, a1, cutSub, cutSub.getRightSequentConnector.child( a2 ) ) )
        }
      case _ => None
    }
}

object RightRankDefinitionLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case definition @ DefinitionLeftRule( subProof, a, m ) if cut.rightSubProof.mainIndices.head != cut.aux2 =>
        val aux2Sub = definition.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, definition.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( DefinitionLeftRule( cutSub, aNew, m ) )
      case _ => None
    }
}

object RightRankDefinitionRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case definition @ DefinitionRightRule( subProof, a, m ) =>
        val aux2Sub = definition.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, definition.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( DefinitionLeftRule( cutSub, aNew, m ) )
      case _ => None
    }
}

object RightRankAndLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case and @ AndLeftRule( subProof, a1, a2 ) if cut.rightSubProof.mainIndices.head != cut.aux2 =>
        val aux2Sub = and.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, and.subProof, aux2Sub )
        val a1New = cutSub.getRightSequentConnector.child( a1 )
        val a2New = cutSub.getRightSequentConnector.child( a2 )
        Some( AndLeftRule( cutSub, a1New, a2New ) )
      case _ => None
    }
}

object RightRankAndRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ AndRightRule( leftSubProof, a1, rightSubProof, a2 ) =>
        val aux2Left = r.getLeftSequentConnector.parents( cut.aux2 )
        val aux2Right = r.getRightSequentConnector.parents( cut.aux2 )

        ( aux2Left, aux2Right ) match {
          // The right cut formula is in the left subproof of the binary inference
          case ( Seq( aux2Sub ), Seq() ) =>
            val cutSub = CutRule(
              cut.leftSubProof, cut.aux1, leftSubProof, aux2Sub )
            Some( AndRightRule(
              cutSub, cutSub.getRightSequentConnector.child( a1 ), rightSubProof, a2 ) )

          // The right cut formula is in the right subproof of the binary inference
          case ( Seq(), Seq( aux2Sub ) ) =>
            val cutSub = CutRule( cut.leftSubProof, cut.aux1, rightSubProof, aux2Sub )
            Some( AndRightRule( leftSubProof, a1, cutSub, cutSub.getRightSequentConnector.child( a2 ) ) )
        }
      case _ => None
    }
}

object RightRankOrLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ OrLeftRule( leftSubProof, a1, rightSubProof, a2 ) if cut.rightSubProof.mainIndices.head != cut.aux2 =>
        val aux2Left = r.getLeftSequentConnector.parents( cut.aux2 )
        val aux2Right = r.getRightSequentConnector.parents( cut.aux2 )

        ( aux2Left, aux2Right ) match {
          // The right cut formula is in the left subproof of the binary inference
          case ( Seq( aux2Sub ), Seq() ) =>
            val cutSub = CutRule( cut.leftSubProof, cut.aux1, leftSubProof, aux2Sub )
            Some( OrLeftRule( cutSub, cutSub.getRightSequentConnector.child( a1 ), rightSubProof, a2 ) )

          // The right cut formula is in the right subproof of the binary inference
          case ( Seq(), Seq( aux2Sub ) ) =>
            val cutSub = CutRule( cut.leftSubProof, cut.aux1, rightSubProof, aux2Sub )
            Some( OrLeftRule( leftSubProof, a1, cutSub, cutSub.getRightSequentConnector.child( a2 ) ) )
        }

      case _ => None
    }
}

object RightRankOrRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ OrRightRule( subProof, a1, a2 ) =>
        val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, r.subProof, aux2Sub )
        val a1New = cutSub.getRightSequentConnector.child( a1 )
        val a2New = cutSub.getRightSequentConnector.child( a2 )
        Some( OrRightRule( cutSub, a1New, a2New ) )

      case _ => None
    }
}

object RightRankImpLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ ImpLeftRule( leftSubProof, a1, rightSubProof, a2 ) if cut.rightSubProof.mainIndices.head != cut.aux2 =>
        val aux2Left = r.getLeftSequentConnector.parents( cut.aux2 )
        val aux2Right = r.getRightSequentConnector.parents( cut.aux2 )

        ( aux2Left, aux2Right ) match {
          // The right cut formula is in the left subproof of the binary inference
          case ( Seq( aux2Sub ), Seq() ) =>
            val cutSub = CutRule( cut.leftSubProof, cut.aux1, leftSubProof, aux2Sub )
            Some( ImpLeftRule( cutSub, cutSub.getRightSequentConnector.child( a1 ), rightSubProof, a2 ) )

          // The right cut formula is in the right subproof of the binary inference
          case ( Seq(), Seq( aux2Sub ) ) =>
            val cutSub = CutRule( cut.leftSubProof, cut.aux1, rightSubProof, aux2Sub )
            Some( ImpLeftRule( leftSubProof, a1, cutSub, cutSub.getRightSequentConnector.child( a2 ) ) )
        }

      case _ => None
    }
}

object RightRankImpRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ ImpRightRule( subProof, a1, a2 ) =>
        val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, r.subProof, aux2Sub )
        val a1New = cutSub.getRightSequentConnector.child( a1 )
        val a2New = cutSub.getRightSequentConnector.child( a2 )
        Some( ImpRightRule( cutSub, a1New, a2New ) )

      case _ => None
    }
}

object RightRankNegLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ NegLeftRule( subProof, a ) if cut.rightSubProof.mainIndices.head != cut.aux2 =>
        val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( NegLeftRule( cutSub, aNew ) )

      case _ => None
    }
}

object RightRankNegRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ NegRightRule( subProof, a ) =>
        val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( NegRightRule( cutSub, aNew ) )

      case _ => None
    }
}

object RightRankForallLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ ForallLeftRule( subProof, a, f, term, quant ) if cut.rightSubProof.mainIndices.head != cut.aux2 =>
        val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( ForallLeftRule( cutSub, aNew, f, term, quant ) )

      case _ => None
    }
}

object RightRankForallRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case right @ ForallRightRule( _, _, _, _ ) if freeVariables( cut.endSequent ).contains( right.eigenVariable ) =>
        val newEigenvariable = rename( right.eigenVariable, freeVariables( cut.endSequent ) )
        val renaming = Substitution( right.eigenVariable -> newEigenvariable )
        val newRightSubProof = right.copy(
          subProof = renaming( right.subProof ), eigenVariable = newEigenvariable )
        reduce( cut.copy( rightSubProof = newRightSubProof ) )

      case right @ ForallRightRule( _, _, _, _ ) =>
        val newSubProof = CutRule(
          cut.leftSubProof,
          cut.aux1,
          right.subProof,
          right.getSequentConnector.parent( cut.aux2 ) )
        Some( right.copy(
          subProof = newSubProof,
          aux = newSubProof.getRightSequentConnector.child( right.aux ) ) )

      case _ => None
    }
}

object RightRankForallSkRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ ForallSkRightRule( subProof, a, main, skTerm, skDef ) =>
        val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( ForallSkRightRule( cutSub, aNew, main, skTerm, skDef ) )

      case _ => None
    }
}

object RightRankExistsLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case right @ ExistsLeftRule( _, _, _, _
        ) if right.mainIndices.head != cut.aux2 && freeVariables( cut.endSequent ).contains( right.eigenVariable ) =>
        val newEigenvariable = rename( right.eigenVariable, freeVariables( cut.endSequent ) )
        val renaming = Substitution( right.eigenVariable -> newEigenvariable )
        val newRightSubProof = right.copy( subProof = renaming( right.subProof ), eigenVariable = newEigenvariable )
        reduce( cut.copy( rightSubProof = newRightSubProof ) )

      case right @ ExistsLeftRule( _, _, _, _ ) if right.mainIndices.head != cut.aux2 =>
        val newSubProof = CutRule(
          cut.leftSubProof,
          cut.aux1,
          right.subProof,
          right.getSequentConnector.parent( cut.aux2 ) )
        Some( right.copy(
          subProof = newSubProof,
          aux = newSubProof.getRightSequentConnector.child( right.aux ) ) )

      case _ => None
    }
}

object RightRankExistsSkLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ ExistsSkLeftRule( subProof, a, main, skTerm, skDef ) if cut.rightSubProof.mainIndices.head != cut.aux2 =>
        val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( ExistsSkLeftRule( cutSub, aNew, main, skTerm, skDef ) )

      case _ => None
    }
}

object RightRankExistsRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ ExistsRightRule( subProof, a, f, term, quant ) =>
        val aux2Sub = r.getSequentConnector.parent( cut.aux2 )
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, r.subProof, aux2Sub )
        val aNew = cutSub.getRightSequentConnector.child( a )
        Some( ExistsRightRule( cutSub, aNew, f, term, quant ) )

      case _ => None
    }
}

object RightRankEqualityLeftReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ EqualityLeftRule( subProof, eq, eaux, indicator
        ) if r.mainIndices.head != cut.aux2 && r.eqInConclusion != cut.aux2 =>
        val conn1 = r.getSequentConnector
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, subProof, conn1.parent( cut.aux2 ) )
        val conn2 = cutSub.getRightSequentConnector
        Some( EqualityLeftRule( cutSub, conn2.child( eq ), conn2.child( eaux ), indicator ) )

      case _ => None
    }
}

object RightRankEqualityRightReduction extends CutReduction {
  def reduce( cut: CutRule ): Option[LKProof] =
    cut.rightSubProof match {
      case r @ EqualityRightRule( subProof, eq, eaux, indicator ) if r.eqInConclusion != cut.aux2 =>
        val conn1 = r.getSequentConnector
        val cutSub = CutRule( cut.leftSubProof, cut.aux1, subProof, conn1.parent( cut.aux2 ) )
        val conn2 = cutSub.getRightSequentConnector
        Some( EqualityRightRule( cutSub, conn2 child eq, conn2 child eaux, indicator ) )

      case _ => None
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
  def apply( cut: CutRule ): Option[LKProof] =
    RightRankWeakeningLeftReduction.reduce( cut ) orElse
      RightRankWeakeningRightReduction.reduce( cut ) orElse
      RightRankContractionLeftReduction.reduce( cut ) orElse
      RightRankContractionRightReduction.reduce( cut ) orElse
      RightRankCutReduction.reduce( cut ) orElse
      RightRankDefinitionLeftReduction.reduce( cut ) orElse
      RightRankDefinitionRightReduction.reduce( cut ) orElse
      RightRankAndLeftReduction.reduce( cut ) orElse
      RightRankAndRightReduction.reduce( cut ) orElse
      RightRankOrLeftReduction.reduce( cut ) orElse
      RightRankOrRightReduction.reduce( cut ) orElse
      RightRankImpLeftReduction.reduce( cut ) orElse
      RightRankImpRightReduction.reduce( cut ) orElse
      RightRankNegLeftReduction.reduce( cut ) orElse
      RightRankNegRightReduction.reduce( cut ) orElse
      RightRankForallLeftReduction.reduce( cut ) orElse
      RightRankForallRightReduction.reduce( cut ) orElse
      RightRankForallSkRightReduction.reduce( cut ) orElse
      RightRankExistsLeftReduction.reduce( cut ) orElse
      RightRankExistsSkLeftReduction.reduce( cut ) orElse
      RightRankExistsRightReduction.reduce( cut ) orElse
      RightRankEqualityLeftReduction.reduce( cut ) orElse
      RightRankEqualityRightReduction.reduce( cut )
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

private object inductionEigenvariables {
  /**
   * Retrieves all of the eigenvariables of a given induction rule.
   * @param induction The induction rule.
   * @return All the eigenvariables of the induction rule.
   */
  def apply( induction: InductionRule ) =
    induction.cases.flatMap( _.eigenVars ).toSet
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

    cut.rightSubProof match {

      case ind @ InductionRule( _, _, _
        ) if contextVariables( cut ) intersect inductionEigenvariables( ind ) nonEmpty =>
        val newEigenvariables = rename( inductionEigenvariables( ind ), contextVariables( cut ) )
        val newInductionCases = ind.cases map { inductionCase =>
          val newCaseEigenvariables = inductionCase.eigenVars.map( newEigenvariables )
          val renaming = Substitution( inductionCase.eigenVars.map { ev => ( ev, newEigenvariables( ev ) ) } )
          inductionCase.copy( proof = renaming( inductionCase.proof ), eigenVars = newCaseEigenvariables )
        }
        val newRightSubProof = ind.copy( cases = newInductionCases )
        apply( cut.copy( rightSubProof = newRightSubProof ) )

      case ind @ InductionRule( _, indFormula, indTerm ) =>
        val targetCase = ind.cases.filter( _.proof.endSequent.antecedent.contains( cut.cutFormula ) ).head
        val newIndCases = ind.cases map {
          indCase =>
            if ( indCase == targetCase ) {
              val subProof = CutRule( cut.leftSubProof, indCase.proof, cut.cutFormula )
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

  private def contextVariables( cut: CutRule ) =
    freeVariables( cut.rightSubProof.endSequent ) ++ freeVariables( cut.leftSubProof.endSequent )
}

object inductionUnfoldingReduction {

  /**
   * Tries to apply the reduction.
   *
   * @param induction See `inductionUnfoldingReduction$.apply(induction:InductionRule)(ctx:Context):Option[LKProof]`
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
   *         `inductionUnfoldingReduction.apply(InductionRule)(Context): Option[LKProof]`.
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
   * @return If the given induction's term is in constructor form a proof of the same end-sequent for
   *         which the induction inference has been unfolded is returned, otherwise None.
   */
  def apply( induction: InductionRule )( implicit ctx: Context ): Option[LKProof] = {
    if ( isConstructorForm( induction.term ) ) {
      Some( unfoldInduction( induction ) )
    } else {
      None
    }
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

    cut.leftSubProof match {
      case ind @ InductionRule( _, _, _ ) if ind.mainIndices.head != cut.aux1 &&
        ( contextVariables( cut ) intersect inductionEigenvariables( ind ) nonEmpty ) =>
        val newEigenvariables = rename( inductionEigenvariables( ind ), contextVariables( cut ) )
        val newInductionCases = ind.cases map { inductionCase =>
          val newCaseEigenvariables = inductionCase.eigenVars.map( newEigenvariables )
          val renaming = Substitution( inductionCase.eigenVars.map { ev => ( ev, newEigenvariables( ev ) ) } )
          inductionCase.copy( proof = renaming( inductionCase.proof ), eigenVars = newCaseEigenvariables )
        }
        val newLeftSubProof = ind.copy( cases = newInductionCases )
        apply( cut.copy( leftSubProof = newLeftSubProof ) )

      case ind @ InductionRule( inductionCases, inductionFormula, inductionTerm
        ) if ind.mainIndices.head != cut.aux1 =>
        val newInductionCases = inductionCases zip ind.occConnectors map {
          case ( inductionCase, connector ) =>
            if ( connector.parentOption( cut.aux1 ).nonEmpty ) {
              val subProof = CutRule(
                inductionCase.proof, connector.parent( cut.aux1 ), cut.rightSubProof, cut.aux2 )
              val hypotheses = inductionCase.hypotheses map { subProof.getLeftSequentConnector.child( _ ) }
              val conclusion = subProof.getLeftSequentConnector.child( inductionCase.conclusion )
              inductionCase.copy( proof = subProof, hypotheses = hypotheses, conclusion = conclusion )
            } else {
              inductionCase
            }
        }
        Some( InductionRule( newInductionCases, inductionFormula, inductionTerm ) )
      case _ => None
    }
  }

  private def contextVariables( cut: CutRule ) =
    freeVariables( cut.rightSubProof.endSequent ) ++ freeVariables( cut.leftSubProof.endSequent )
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
      inductionReduction( cut ) map { super.recurse( _, () ) }

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
