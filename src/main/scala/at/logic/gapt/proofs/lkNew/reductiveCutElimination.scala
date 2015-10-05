/*
/*
 * ReductiveCutElim.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._
import at.logic.gapt.proofs.SequentIndex

class ReductiveCutElimException( msg: String ) extends Exception( msg )

/**
 * This object implements a version of Gentzen's cut-elimination
 * proof for our sequent calculus LK. For details, please
 * refer to the documentation of the apply methods.
 */

object ReductiveCutElimination {
  // This list stores a list of subproofs that are reduced
  // during the run of the algorithm.
  private var proofList: List[LKProof] = Nil
  private var steps = false

  /**
   * After calling apply with steps = true, the list of
   * proofs arising during cut-elimination can be obtained
   * from this method.
   *
   * @return The list of proofs arising during cut-elimination
   * after apply() has been called. Nil otherwise.
   */
  def proofs = proofList
  def proofs_=( plist: List[LKProof] ) = proofList = plist

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
   * Note: We assume that proof is regular, i.e. that an eigenvariable
   * of a quantifier rule in proof is used by exactly one such quantifier rule.
   * Further regularization is done during cut-elimination whenever necessary.
   *
   * @param proof The proof to subject to cut-elimination.
   * @param _steps Collect the list of subproofs arising during cut-elimination.
   * This list can be obtained by the proofs method.
   * @param pred_done A predicate deciding when to terminate the algorithm.
   * @param pred_cut A predicate deciding whether or not to reduce a cut encountered
   * when traversing the proof.
   *
   * @return The proof as it is after pred_done returns true.
   */
  def apply( proof: LKProof, _steps: Boolean, pred_done: LKProof => Boolean, pred_cut: ( LKProof, LKProof ) => Boolean ): LKProof = {
    steps = _steps

    proofList = proof :: Nil
    // var pr = regularize(proof)
    var pr = proof
    do {
      def pred( local: LKProof ) = pred_cut( pr, local )
      val p = cutElim( pr )( pred )
      pr = cleanStructuralRules( p )
      if ( steps ) proofList = proofList ::: ( pr :: Nil )
    } while ( !pred_done( pr ) && !isCutFree( pr ) )
    if ( !steps ) proofList = proofList ::: ( pr :: Nil )
    pr
  }

  /**
   * This methods implements a version of Gentzen's cut-elimination
   * proof using the (known to be terminating) strategy of reducing
   * a left-uppermost cut. The algorithm terminates when all cuts
   * have been eliminated.
   *
   * @param proof The proof to subject to cut-elimination.
   * @param steps Collect the list of subproofs arising during cut-elimination.
   * @return The cut-free proof.
   */
  def apply( proof: LKProof, steps: Boolean = false ) = eliminateAllByUppermost( proof, steps )

  /**
   * This methods implements a version of Gentzen's cut-elimination
   * proof using the (known to be terminating) strategy of reducing
   * a left-uppermost cut. The algorithm terminates when all cuts
   * have been eliminated.
   *
   * @param proof The proof to subject to cut-elimination.
   * @param steps Collect the list of subproofs arising during cut-elimination.
   * @return The cut-free proof.
   */
  def eliminateAllByUppermost( proof: LKProof, steps: Boolean ): LKProof =
    apply( proof, steps, { x => false },
    { ( _, cut ) => cut match { case CutRule( leftSubProof, _, rightSubProof, _ ) =>
      isCutFree( leftSubProof ) && isCutFree( rightSubProof ) } } )

  /**
   * This method checks whether a proof is cut-free.
   *
   * @param proof The proof to check for cut-freeness.
   * @return True if proof does not contain the cut rule, False otherwise.
   */
  def isCutFree( proof: LKProof ): Boolean = proof match {
    case InitialSequent(_)      => true
    case UnaryLKProof(_, subProof) => isCutFree( subProof )
    case p: CutRule => false
    case BinaryLKProof(_, leftSubProof, rightSubProof) =>
      isCutFree( leftSubProof ) && isCutFree( rightSubProof )
  }

  // Implements the Gentzen cut-reduction rules.
  private def cutElim( proof: LKProof )( implicit pred: LKProof => Boolean ): LKProof = proof match {
    case InitialSequent( _ )                                 =>
      proof

    case WeakeningLeftRule( subProof, formula )             =>
      WeakeningLeftRule( cutElim( subProof ), formula )

    case WeakeningRightRule( subProof, formula )            =>
      WeakeningRightRule( cutElim( subProof ), formula )

    case ContractionLeftRule( subProof, _, _ )    =>
      ContractionLeftRule( cutElim( subProof ), proof.mainFormulas.head )

    case ContractionRightRule( subProof, _, _ )   =>
      ContractionRightRule( cutElim( subProof ), proof.mainFormulas.head )

    case AndRightRule( leftSubProof, _, rightSubProof, _ ) =>
      AndRightRule( cutElim( leftSubProof ), cutElim( rightSubProof ), proof.mainFormulas.head)

    case AndLeftRule( subProof, _, _ ) =>
      AndLeftRule(cutElim(subProof), proof.mainFormulas.head)

    case OrLeftRule( leftSubProof, _, rightSubProof, _ ) =>
      OrLeftRule( cutElim( leftSubProof ), cutElim( rightSubProof ), proof.mainFormulas.head)

    case OrRightRule( subProof, _, _ ) =>
      OrRightRule(cutElim(subProof), proof.mainFormulas.head)

    case ImpLeftRule( leftSubProof, _, rightSubProof, _ )     =>
      ImpLeftRule( cutElim( leftSubProof ), cutElim( rightSubProof ), proof.mainFormulas.head )

    case ImpRightRule( subProof, _, _ )          =>
      ImpRightRule( cutElim( subProof ), proof.mainFormulas.head )

    case NegLeftRule( subProof, _ )                  =>
      NegLeftRule( cutElim( subProof ), proof.auxFormulas.head.head )

    case NegRightRule( subProof, _ )                  =>
      NegRightRule( cutElim( subProof ), proof.auxFormulas.head.head )

    case ForallLeftRule( subProof, _, _, term, _ )      =>
      ForallLeftRule( cutElim( subProof ), proof.mainFormulas.head, term )

    case ForallRightRule( subProof, _, _, eigen, _ ) =>
      ForallRightRule( cutElim( subProof ), proof.mainFormulas.head, eigen )

    case ExistsLeftRule( subProof, _, _, eigen, _ ) =>
      ExistsLeftRule( cutElim( subProof ), proof.mainFormulas.head, eigen )

    case ExistsRightRule( subProof, _, _, term, _ )      =>
      ExistsRightRule( cutElim( subProof ), proof.mainFormulas.head, term )

    case EqualityLeftRule( subProof, _ , _, _ ) =>
      EqualityLeftRule( cutElim( subProof ), proof.auxFormulas.head(0), proof.auxFormulas.head(1), proof.mainFormulas.head )

    case EqualityRightRule( subProof, _ , _, _ ) =>
      EqualityRightRule( cutElim( subProof ), proof.auxFormulas.head(0), proof.auxFormulas.head(1), proof.mainFormulas.head )

    case CutRule( leftSubProof,aux1, rightSubProof, aux2 ) =>
      if ( pred( proof ) )
        reduceCut( leftSubProof, aux1, rightSubProof, aux2 )
      else
        CutRule( cutElim( leftSubProof ), cutElim( rightSubProof ), proof.auxFormulas.head.head )
  }

  private def reduceCut( left: LKProof, aux1: SequentIndex, right: LKProof, aux2: SequentIndex): LKProof =
    reduceGrade( left, aux1, right, aux2 )

  // Grade reduction rules:
  private def reduceGrade( left: LKProof, aux1: SequentIndex, right: LKProof, aux2: SequentIndex ): LKProof =
    ( left, right ) match {
      case ( AndRightRule( llSubProof, a1, lrSubProof, a2), AndLeftRule( rSubProof, a3, a4) ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val tmp = CutRule( lrSubProof, a2,  rSubProof, a4 )
        val o = tmp.getRightOccConnector
        CutRule(llSubProof, a1, tmp, o.children(a3).head)

      case ( OrRightRule( lSubProof, a1, a2 ), OrLeftRule( rlSubProof, a3, rrSubProof, a4 ) ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val tmp = CutRule( lSubProof, a1, rlSubProof, a3 )
        val o = tmp.getLeftOccConnector
        CutRule(tmp, o.children(a2).head, rrSubProof, a4)

      case ( ImpRightRule( lSubProof, a1, a2 ), ImpLeftRule( rlSubProof, a3, rrSubProof, a4 ) ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val tmp = CutRule( lSubProof, a1, rlSubProof, a3 )
        val o = tmp.getLeftOccConnector
        CutRule(tmp, o.children(a2).head, rrSubProof, a4)

      case ( NegRightRule( lSubProof, a1 ), NegLeftRule( rSubProof, a2 ) ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        CutRule( rSubProof, a2, lSubProof, a1 )

      case _ => reduceGradeQ( left, aux1, right, aux2)
    }

  private def reduceGradeQ( left: LKProof, aux1: SequentIndex, right: LKProof, aux2: SequentIndex ): LKProof =
    ( left, right ) match {
      case ( ForallRightRule( lSubProof, a1, eigen, quant ), ForallLeftRule( rSubProof, a2, f, term, quant ) if left.mainIndices.head == aux1 && right.mainIndices.head == aux2 =>
        val up = applySubstitution( up1, Substitution( eigenVar, term ) )._1
        CutRule( up, up2, aux2.formula )
      case ( ExistsRightRule( up1, _, aux1, prin1, term ), ExistsLeftRule( up2, _, aux2, prin2, eigenVar ) ) if ( prin1.formula == cutFormula1 && prin2.formula == cutFormula2 ) =>
        val up = applySubstitution( up2, Substitution( eigenVar, term ) )._1
        CutRule( up1, up, aux1.formula )
      case ( DefinitionRightRule( up1, _, aux1, prin1 ), DefinitionLeftRule( up2, _, aux2, prin2 ) ) if ( prin1.formula == cutFormula1 && prin2.formula == cutFormula2 ) =>
        CutRule( up1, up2, aux1, aux2 )
      case _ => reduceRank( left, right, cutFormula1, cutFormula2 )
    }

  // Rank reduction rules:
  private def reduceRank( left: LKProof, right: LKProof, cutFormula1: HOLFormula, cutFormula2: HOLFormula ): LKProof =
    ( left, right ) match {
      case ( Axiom( seq ), proof: LKProof ) if ( seq.isTaut ) => proof
      case ( proof: LKProof, Axiom( seq ) ) if ( seq.isTaut ) => proof
      // This is a case for nontautological axioms
      case ( ax1: NullaryLKProof, ax2: NullaryLKProof ) =>
        val seq = CutRule( ax1, ax2, cutFormula1 ).root.toHOLSequent
        Axiom( seq.antecedent, seq.succedent )
      //case (WeakeningRightRule(up, _, prin), proof: LKProof) => //Can't match this, why??? Fixed: moved as a subcase of UnaryLKProof
      case ( proof: LKProof, WeakeningLeftRule( up, _, prin ) ) =>
        if ( prin.formula == cutFormula2 ) {
          var tmp: LKProof = up
          var alreadySeen = false
          for ( i <- proof.root.antecedent ) tmp = WeakeningLeftRule( tmp, i.formula )
          for ( i <- proof.root.succedent )
            if ( i.formula != cutFormula1 || alreadySeen ) tmp = WeakeningRightRule( tmp, i.formula )
            else alreadySeen = true
          tmp
        } else WeakeningLeftRule( CutRule( proof, up, cutFormula2 ), prin.formula )
      //case (ContractionRightRule(up, _, aux1, aux2, prin), proof: LKProof) => //Can't match this, why??? Fixed: moved as a subcase of UnaryLKProof
      case ( proof: LKProof, ContractionLeftRule( up, _, aux1, aux2, prin ) ) =>
        if ( prin.formula == cutFormula2 ) {
          val proof1 = regularize( proof )
          var tmp: LKProof = CutRule( proof1, CutRule( proof, up, aux1.formula ), aux2.formula )
          var alreadySeen = false
          for ( i <- proof.root.antecedent ) tmp = ContractionLeftRule( tmp, i.formula )
          for ( i <- proof.root.succedent )
            if ( i.formula != cutFormula1 || alreadySeen ) tmp = ContractionRightRule( tmp, i.formula )
            else alreadySeen = true
          regularize( tmp )
        } else ContractionLeftRule( CutRule( proof, up, cutFormula2 ), aux1.formula )
      // These are cases for nontautological axioms on the left (cases on the right are not needed because, since we
      // first reduce rank on the left, when it reaches nontautological axiom on the right, previous case is applicable)
      case ( ax: NullaryLKProof, proof: UnaryLKProof )  => reduceUnaryRight( ax, proof, cutFormula1 )
      case ( ax: NullaryLKProof, proof: BinaryLKProof ) => reduceBinaryRight( ax, proof, cutFormula1 )
      case ( unary: UnaryLKProof, proof: LKProof ) =>
        if ( unary.rule == WeakeningRightRuleType ) {
          val nLine = sys.props( "line.separator" )
          val unap = WeakeningRightRule.unapply( unary )
          if ( unap == None )
            throw new ReductiveCutElimException( "Can't match case: " + nLine + " cut left premice is: " + unary.toString.replaceAll( ",", nLine ) +
              nLine + nLine + " cut right premice is: " + proof.toString.replaceAll( ",", nLine ) )
          val up = unap.get._1
          val prin = unap.get._3
          if ( prin.formula == cutFormula1 ) {
            var tmp: LKProof = up
            var alreadySeen = false
            for ( i <- proof.root.antecedent )
              if ( i.formula != cutFormula2 || alreadySeen ) tmp = WeakeningLeftRule( tmp, i.formula )
              else alreadySeen = true
            for ( i <- proof.root.succedent ) tmp = WeakeningRightRule( tmp, i.formula )
            tmp
          } else WeakeningRightRule( CutRule( up, proof, cutFormula1 ), prin.formula )
        } else if ( unary.rule == ContractionRightRuleType ) {
          val unap = ContractionRightRule.unapply( unary )
          val nLine = sys.props( "line.separator" )
          if ( unap == None )
            throw new ReductiveCutElimException( "Can't match case: " + nLine + " cut left premice is: " + unary.toString.replaceAll( ",", nLine ) +
              nLine + nLine + " cut right premice is: " + proof.toString.replaceAll( ",", nLine ) )
          val up = unap.get._1
          val aux1 = unap.get._3
          val aux2 = unap.get._4
          val prin = unap.get._5
          if ( prin.formula == cutFormula1 ) {
            val proof1 = regularize( proof )
            var tmp: LKProof = CutRule( CutRule( up, proof, aux1.formula ), proof1, aux2.formula )
            var alreadySeen = false
            for ( i <- proof.root.antecedent )
              if ( i.formula != cutFormula2 || alreadySeen ) tmp = ContractionLeftRule( tmp, i.formula )
              else alreadySeen = true
            for ( i <- proof.root.succedent ) tmp = ContractionRightRule( tmp, i.formula )
            regularize( tmp )
          } else ContractionRightRule( CutRule( up, proof, cutFormula1 ), aux1.formula )
        } else reduceUnaryLeft( unary, proof, cutFormula1 )
      case ( binary: BinaryLKProof, proof: LKProof ) => reduceBinaryLeft( binary, proof, cutFormula1 )
      case _ =>
        throw new ReductiveCutElimException( "Can't match the case: Cut(" + left.rule.toString + ", " + right.rule.toString + ")" )
    }

  private def reduceUnaryLeft( unary: UnaryLKProof, proof: LKProof, cutFormula: HOLFormula ): LKProof = unary match {
    case WeakeningLeftRule( up, _, prin ) =>
      WeakeningLeftRule( CutRule( up, proof, cutFormula ), prin.formula )
    case ContractionLeftRule( up, _, aux, _, prin ) =>
      ContractionLeftRule( CutRule( up, proof, cutFormula ), aux.formula )
    case DefinitionLeftRule( up, _, aux, prin ) =>
      DefinitionLeftRule( CutRule( up, proof, cutFormula ), aux.formula, prin.formula )
    case DefinitionRightRule( up, _, aux, prin ) if ( prin.formula != cutFormula ) =>
      DefinitionRightRule( CutRule( up, proof, cutFormula ), aux.formula, prin.formula )
    case AndLeft1Rule( up, _, aux, prin ) => prin.formula match {
      case And( aux.formula, f ) => AndLeft1Rule( CutRule( up, proof, cutFormula ), aux.formula, f )
    }
    case AndLeft2Rule( up, _, aux, prin ) => prin.formula match {
      case And( f, aux.formula ) => AndLeft2Rule( CutRule( up, proof, cutFormula ), f, aux.formula )
    }
    case OrRight1Rule( up, _, aux, prin ) if prin.formula != cutFormula => prin.formula match {
      case Or( aux.formula, f ) => OrRight1Rule( CutRule( up, proof, cutFormula ), aux.formula, f )
    }
    case OrRight2Rule( up, _, aux, prin ) if prin.formula != cutFormula => prin.formula match {
      case Or( f, aux.formula ) => OrRight2Rule( CutRule( up, proof, cutFormula ), f, aux.formula )
    }
    case ImpRightRule( up, _, aux1, aux2, prin ) if prin.formula != cutFormula =>
      ImpRightRule( CutRule( up, proof, cutFormula ), aux1.formula, aux2.formula )
    case NegLeftRule( up, _, aux, prin ) =>
      NegLeftRule( CutRule( up, proof, cutFormula ), aux.formula )
    case NegRightRule( up, _, aux, prin ) if prin.formula != cutFormula =>
      NegRightRule( CutRule( up, proof, cutFormula ), aux.formula )
    case ForallLeftRule( up, _, aux, prin, term ) =>
      ForallLeftRule( CutRule( up, proof, cutFormula ), aux.formula, prin.formula, term )
    case ForallRightRule( up, _, aux, prin, eigenVar ) if prin.formula != cutFormula =>
      ForallRightRule( CutRule( up, proof, cutFormula ), aux.formula, prin.formula, eigenVar )
    case ExistsLeftRule( up, _, aux, prin, eigenVar ) =>
      ExistsLeftRule( CutRule( up, proof, cutFormula ), aux.formula, prin.formula, eigenVar )
    case ExistsRightRule( up, _, aux, prin, term ) if prin.formula != cutFormula =>
      ExistsRightRule( CutRule( up, proof, cutFormula ), aux.formula, prin.formula, term )
    case _ => proof match {
      case p: UnaryLKProof  => reduceUnaryRight( unary, p, cutFormula )
      case p: BinaryLKProof => reduceBinaryRight( unary, p, cutFormula )
    }
  }

  private def reduceUnaryRight( proof: LKProof, unary: UnaryLKProof, cutFormula: HOLFormula ): LKProof = unary match {
    case WeakeningRightRule( up, _, prin ) =>
      WeakeningRightRule( CutRule( proof, up, cutFormula ), prin.formula )
    case ContractionRightRule( up, _, aux, _, prin ) =>
      ContractionRightRule( CutRule( proof, up, cutFormula ), aux.formula )
    case DefinitionLeftRule( up, _, aux, prin ) if ( prin.formula != cutFormula ) =>
      DefinitionLeftRule( CutRule( proof, up, cutFormula ), aux.formula, prin.formula )
    case DefinitionRightRule( up, _, aux, prin ) =>
      DefinitionRightRule( CutRule( proof, up, cutFormula ), aux.formula, prin.formula )
    case AndLeft1Rule( up, _, aux, prin ) if prin.formula != cutFormula => prin.formula match {
      case And( aux.formula, f ) => AndLeft1Rule( CutRule( proof, up, cutFormula ), aux.formula, f )
    }
    case AndLeft2Rule( up, _, aux, prin ) if prin.formula != cutFormula => prin.formula match {
      case And( f, aux.formula ) => AndLeft2Rule( CutRule( proof, up, cutFormula ), f, aux.formula )
    }
    case OrRight1Rule( up, _, aux, prin ) => prin.formula match {
      case Or( aux.formula, f ) => OrRight1Rule( CutRule( proof, up, cutFormula ), aux.formula, f )
    }
    case OrRight2Rule( up, _, aux, prin ) => prin.formula match {
      case Or( f, aux.formula ) => OrRight2Rule( CutRule( proof, up, cutFormula ), f, aux.formula )
    }
    case ImpRightRule( up, _, aux1, aux2, prin ) =>
      ImpRightRule( CutRule( proof, up, cutFormula ), aux1.formula, aux2.formula )
    case NegLeftRule( up, _, aux, prin ) if prin.formula != cutFormula =>
      NegLeftRule( CutRule( proof, up, cutFormula ), aux.formula )
    case NegRightRule( up, _, aux, prin ) =>
      NegRightRule( CutRule( proof, up, cutFormula ), aux.formula )
    case ForallLeftRule( up, _, aux, prin, term ) if prin.formula != cutFormula =>
      ForallLeftRule( CutRule( proof, up, cutFormula ), aux.formula, prin.formula, term )
    case ForallRightRule( up, _, aux, prin, eigenVar ) =>
      ForallRightRule( CutRule( proof, up, cutFormula ), aux.formula, prin.formula, eigenVar )
    case ExistsLeftRule( up, _, aux, prin, eigenVar ) if prin.formula != cutFormula =>
      ExistsLeftRule( CutRule( proof, up, cutFormula ), aux.formula, prin.formula, eigenVar )
    case ExistsRightRule( up, _, aux, prin, term ) =>
      ExistsRightRule( CutRule( proof, up, cutFormula ), aux.formula, prin.formula, term )
    case _ =>
      throw new ReductiveCutElimException( "Can't match the case: Cut(" + proof.rule.toString + ", " + unary.rule.toString + ")" )
  }

  private def reduceBinaryLeft( binary: BinaryLKProof, proof: LKProof, cutFormula: HOLFormula ): LKProof = binary match {
    case AndRightRule( up1, up2, _, aux1, aux2, prin ) if prin.formula != cutFormula =>
      if ( ( aux1.formula != cutFormula && up1.root.succedent.exists( x => x.formula == cutFormula ) ) ||
        ( aux1.formula == cutFormula && up1.root.succedent.find( x => x.formula == cutFormula ).size > 1 ) )
        AndRightRule( CutRule( up1, proof, cutFormula ), up2, aux1.formula, aux2.formula )
      else if ( ( aux2.formula != cutFormula && up2.root.succedent.exists( x => x.formula == cutFormula ) ) ||
        ( aux2.formula == cutFormula && up2.root.succedent.find( x => x.formula == cutFormula ).size > 1 ) )
        AndRightRule( up1, CutRule( up2, proof, cutFormula ), aux1.formula, aux2.formula )
      else throw new ReductiveCutElimException( "Can't find cut-formula!" )
    case OrLeftRule( up1, up2, _, aux1, aux2, prin ) =>
      if ( up1.root.succedent.exists( x => x.formula == cutFormula ) )
        OrLeftRule( CutRule( up1, proof, cutFormula ), up2, aux1.formula, aux2.formula )
      else if ( up2.root.succedent.exists( x => x.formula == cutFormula ) )
        OrLeftRule( up1, CutRule( up2, proof, cutFormula ), aux1.formula, aux2.formula )
      else throw new ReductiveCutElimException( "Can't find cut-formula!" )
    case ImpLeftRule( up1, up2, _, aux1, aux2, prin ) =>
      if ( ( aux1.formula != cutFormula && up1.root.succedent.exists( x => x.formula == cutFormula ) ) ||
        ( aux1.formula == cutFormula && up1.root.succedent.find( x => x.formula == cutFormula ).size > 1 ) )
        ImpLeftRule( CutRule( up1, proof, cutFormula ), up2, aux1.formula, aux2.formula )
      else if ( up2.root.succedent.exists( x => x.formula == cutFormula ) )
        ImpLeftRule( up1, CutRule( up2, proof, cutFormula ), aux1.formula, aux2.formula )
      else throw new ReductiveCutElimException( "Can't find cut-formula!" )
    //Following line is redundant when eliminating uppermost cut
    case CutRule( up1, up2, _, a1, a2 ) => if ( up1.root.succedent.exists( x => x.formula == cutFormula ) ||
      up1.root.succedent.find( x => x.formula == cutFormula ).size > 1 )
      CutRule( CutRule( up1, proof, cutFormula ), up2, a1.formula )
    else if ( up2.root.succedent.exists( x => x.formula == cutFormula ) )
      CutRule( up1, CutRule( up2, proof, cutFormula ), a1.formula )
    else throw new ReductiveCutElimException( "Can't find cut-formula!" )

    case _ => proof match {
      case p: UnaryLKProof  => reduceUnaryRight( binary, p, cutFormula )
      case p: BinaryLKProof => reduceBinaryRight( binary, p, cutFormula )
    }
  }

  private def reduceBinaryRight( proof: LKProof, binary: BinaryLKProof, cutFormula: HOLFormula ): LKProof = binary match {
    case AndRightRule( up1, up2, _, aux1, aux2, prin ) =>
      if ( up1.root.antecedent.exists( x => x.formula == cutFormula ) )
        AndRightRule( CutRule( proof, up1, cutFormula ), up2, aux1.formula, aux2.formula )
      else if ( up2.root.antecedent.exists( x => x.formula == cutFormula ) )
        AndRightRule( up1, CutRule( proof, up2, cutFormula ), aux1.formula, aux2.formula )
      else throw new ReductiveCutElimException( "Can't find cut-formula!" )
    case OrLeftRule( up1, up2, _, aux1, aux2, prin ) if prin.formula != cutFormula =>
      if ( ( aux1.formula != cutFormula && up1.root.antecedent.exists( x => x.formula == cutFormula ) ) ||
        ( aux1.formula == cutFormula && up1.root.antecedent.find( x => x.formula == cutFormula ).size > 1 ) )
        OrLeftRule( CutRule( proof, up1, cutFormula ), up2, aux1.formula, aux2.formula )
      else if ( ( aux2.formula != cutFormula && up2.root.antecedent.exists( x => x.formula == cutFormula ) ) ||
        ( aux2.formula == cutFormula && up2.root.antecedent.find( x => x.formula == cutFormula ).size > 1 ) )
        OrLeftRule( up1, CutRule( proof, up2, cutFormula ), aux1.formula, aux2.formula )
      else throw new ReductiveCutElimException( "Can't find cut-formula!" )
    case ImpLeftRule( up1, up2, _, aux1, aux2, prin ) if prin.formula != cutFormula =>
      if ( up1.root.antecedent.exists( x => x.formula == cutFormula ) )
        ImpLeftRule( CutRule( proof, up1, cutFormula ), up2, aux1.formula, aux2.formula )
      else if ( ( aux2.formula != cutFormula && up2.root.antecedent.exists( x => x.formula == cutFormula ) ) ||
        ( aux2.formula == cutFormula && up2.root.antecedent.find( x => x.formula == cutFormula ).size > 1 ) )
        ImpLeftRule( up1, CutRule( proof, up2, cutFormula ), aux1.formula, aux2.formula )
      else throw new ReductiveCutElimException( "Can't find cut-formula!" )
    //Following line is redundant when eliminating uppermost cut
    case CutRule( up1, up2, _, a1, a2 ) => if ( up1.root.antecedent.exists( x => x.formula == cutFormula ) )
      CutRule( CutRule( proof, up1, cutFormula ), up2, a1.formula )
    else if ( up2.root.antecedent.exists( x => x.formula == cutFormula ) ||
      up2.root.antecedent.find( x => x.formula == cutFormula ).size > 1 )
      CutRule( up1, CutRule( proof, up2, cutFormula ), a1.formula )
    else throw new ReductiveCutElimException( "Can't find cut-formula!" )
    case _ =>
      throw new ReductiveCutElimException( "Can't match the case: Cut(" + proof.rule.toString + ", " + binary.rule.toString + ")" )
  }
}
*/
