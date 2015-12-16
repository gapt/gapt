package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.occurrences.FormulaOccurrence
import at.logic.gapt.proofs.{ SequentIndex, Sequent, Ant, lkOld }
import at.logic.gapt.proofs.lkOld.base.{ PrincipalFormulas, OccSequent, RichOccSequent }

import scala.collection.immutable.HashMap

/**
 * Conversion algorithm for new LK => old LK
 *
 */
object lkNew2Old {

  /**
   * Converts a proof from new to old LK.
   *
   * @param proof A new LKProof.
   * @return The corresponding old LKProof.
   */
  def apply( proof: LKProof ): lkOld.base.LKProof = apply_( proof )._1

  /**
   * Does the actual converting.
   *
   * @param proof A new LKProof.
   * @return A pair (old LKProof, OccSequent), where the sequent contains the formula occurrences in the old proof that
   *         correspond to indices in the new proof.
   */
  private def apply_( proof: LKProof ): ( lkOld.base.LKProof, OccSequent ) = proof match {
    case LogicalAxiom( atom ) =>
      val ax = lkOld.Axiom( atom )
      testCorrectness( ax, proof, ax.root )

    case ReflexivityAxiom( t ) =>
      val ax = lkOld.Axiom( Seq(), Seq( Eq( t, t ) ) )
      testCorrectness( ax, proof, ax.root )

    case TopAxiom =>
      val ax = lkOld.Axiom( Seq(), Seq( Top() ) )
      testCorrectness( ax, proof, ax.root )

    case BottomAxiom =>
      val ax = lkOld.Axiom( Seq( Bottom() ), Seq() )
      testCorrectness( ax, proof, ax.root )

    case TheoryAxiom( sequent ) =>
      val ax = lkOld.Axiom( sequent )
      testCorrectness( ax, proof, ax.root )

    case WeakeningLeftRule( subProof, formula ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lkOld.WeakeningLeftRule( subProofOld, formula )

      testCorrectness( proofOld, proof, proofOld.prin.head +: sequent.map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case WeakeningRightRule( subProof, formula ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lkOld.WeakeningRightRule( subProofOld, formula )

      testCorrectness( proofOld, proof, sequent.map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case ContractionLeftRule( subProof, aux1, aux2 ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lkOld.ContractionLeftRule( subProofOld, sequent( aux1 ), sequent( aux2 ) )

      testCorrectness( proofOld, proof, proofOld.prin.head +: sequent.delete( aux1, aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case ContractionRightRule( subProof, aux1, aux2 ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lkOld.ContractionRightRule( subProofOld, sequent( aux1 ), sequent( aux2 ) )

      testCorrectness( proofOld, proof, sequent.delete( aux1, aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofOld, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofOld, rightSequent ) = apply_( rightSubProof )
      val proofOld = lkOld.CutRule( leftSubProofOld, rightSubProofOld, leftSequent( aux1 ), rightSequent( aux2 ) )

      testCorrectness( proofOld, proof, leftSequent.delete( aux1 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case NegLeftRule( subProof, aux ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lkOld.NegLeftRule( subProofOld, sequent( aux ) )

      testCorrectness( proofOld, proof, proofOld.prin.head +: sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case NegRightRule( subProof, aux ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lkOld.NegRightRule( subProofOld, sequent( aux ) )

      testCorrectness( proofOld, proof, sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case AndLeftRule( subProof, aux1, aux2 ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lkOld.AndLeftRule( subProofOld, sequent( aux1 ), sequent( aux2 ) )

      testCorrectness( proofOld, proof, proofOld.prin.head +: sequent.delete( aux1, aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofOld, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofOld, rightSequent ) = apply_( rightSubProof )
      val proofOld = lkOld.AndRightRule( leftSubProofOld, rightSubProofOld, leftSequent( aux1 ), rightSequent( aux2 ) )

      testCorrectness( proofOld, proof, ( leftSequent.delete( aux1 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ) :+ proofOld.prin.head )

    case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofOld, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofOld, rightSequent ) = apply_( rightSubProof )
      val proofOld = lkOld.OrLeftRule( leftSubProofOld, rightSubProofOld, leftSequent( aux1 ), rightSequent( aux2 ) )

      testCorrectness( proofOld, proof, proofOld.prin.head +: ( leftSequent.delete( aux1 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ) )

    case OrRightRule( subProof, aux1, aux2 ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lkOld.OrRightRule( subProofOld, sequent( aux1 ), sequent( aux2 ) )

      testCorrectness( proofOld, proof, sequent.delete( aux1, aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofOld, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofOld, rightSequent ) = apply_( rightSubProof )
      val proofOld = lkOld.ImpLeftRule( leftSubProofOld, rightSubProofOld, leftSequent( aux1 ), rightSequent( aux2 ) )

      testCorrectness( proofOld, proof, proofOld.prin.head +: ( leftSequent.delete( aux1 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ) )

    case ImpRightRule( subProof, aux1, aux2 ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lkOld.ImpRightRule( subProofOld, sequent( aux1 ), sequent( aux2 ) )

      testCorrectness( proofOld, proof, sequent.delete( aux1, aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case ForallLeftRule( subProof, aux, f, t, v ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lkOld.ForallLeftRule( subProofOld, sequent( aux ), All( v, f ), t )

      testCorrectness( proofOld, proof, proofOld.prin.head +: sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case ForallRightRule( subProof, aux, eigen, quant ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lkOld.ForallRightRule( subProofOld, sequent( aux ), proof.mainFormulas.head, eigen )

      testCorrectness( proofOld, proof, sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.asInstanceOf[PrincipalFormulas].prin.head )

    case ExistsLeftRule( subProof, aux, eigen, quant ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lkOld.ExistsLeftRule( subProofOld, sequent( aux ), proof.mainFormulas.head, eigen )

      testCorrectness( proofOld, proof, proofOld.asInstanceOf[PrincipalFormulas].prin.head +: sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case ExistsRightRule( subProof, aux, f, t, v ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lkOld.ExistsRightRule( subProofOld, sequent( aux ), Ex( v, f ), t )

      testCorrectness( proofOld, proof, sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case EqualityLeftRule( subProof, eq, aux, pos ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val equation = proof.auxFormulas.head.head
      val ax = lkOld.Axiom( equation )
      val proofOld_ = lkOld.EquationLeftRule( ax, subProofOld, ax.root.succedent.head, sequent( aux ), pos )
      val proofOld = lkOld.ContractionLeftRule( proofOld_, proofOld_.getDescendantInLowerSequent( ax.root.antecedent.head ).get, proofOld_.getDescendantInLowerSequent( sequent( eq ) ).get )

      val mainOcc = proofOld.getDescendantInLowerSequent( proofOld_.prin.head ).get
      testCorrectness( proofOld, proof, mainOcc +: sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case EqualityRightRule( subProof, eq, aux, pos ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val equation = proof.auxFormulas.head.head
      val ax = lkOld.Axiom( equation )
      val proofOld_ = lkOld.EquationRightRule( ax, subProofOld, ax.root.succedent.head, sequent( aux ), pos )
      val proofOld = lkOld.ContractionLeftRule( proofOld_, proofOld_.getDescendantInLowerSequent( ax.root.antecedent.head ).get, proofOld_.getDescendantInLowerSequent( sequent( eq ) ).get )

      val mainOcc = proofOld.getDescendantInLowerSequent( proofOld_.prin.head ).get
      testCorrectness( proofOld, proof, sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case DefinitionLeftRule( subProof, aux, main ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lkOld.DefinitionLeftRule( subProofOld, sequent( aux ), main )

      testCorrectness( proofOld, proof, proofOld.prin.head +: sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case DefinitionRightRule( subProof, aux, main ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lkOld.DefinitionRightRule( subProofOld, sequent( aux ), main )

      testCorrectness( proofOld, proof, sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )
  }

  /**
   * Tests whether the conversion has been performed correctly. Was used for debugging.
   *
   * @param oldProof
   * @param newProof
   * @param sequent
   * @return
   */
  private def testCorrectness( oldProof: lkOld.base.LKProof, newProof: LKProof, sequent: OccSequent ): ( lkOld.base.LKProof, OccSequent ) = {
    oldProof.root.elements.foreach { o =>
      val i = try {
        sequent indexOf o
      } catch {
        case e: NoSuchElementException => throw new Exception( s"Occurrence $o not found in sequent $sequent" )
      }
      if ( newProof.endSequent( i ) != o.formula )
        throw new Exception( s" New2Old: Incorrect sequent for oldproof = $oldProof, newproof = $newProof, sequent = $sequent at index $i: formula should be ${o.formula}, but is ${newProof.endSequent( i )}}." )
    }

    ( oldProof, sequent )
  }
}

/**
 * Conversion algorithm for old LK => new LK.
 *
 */
object lkOld2New {

  /**
   * Converts a proof from old to new LK.
   *
   * @param proof An old LKProof.
   * @return The corresponding new LKProof.
   */
  def apply( proof: lkOld.base.LKProof ): LKProof = apply_( proof )._1

  /**
   * Does the actual converting.
   *
   * @param proof An old LKProof.
   * @return A pair (new LKProof, OccSequent), where the sequent contains the formula occurrences in the old proof that
   *         correspond to indices in the new proof.
   */
  private def apply_( proof: lkOld.base.LKProof ): ( LKProof, OccSequent ) = proof match {
    case lkOld.Axiom( sequent ) =>
      val proofNew = Axiom( sequent.toHOLSequent )

      testCorrectness( proof, proofNew, sequent )

    case lkOld.WeakeningLeftRule( subProof, _, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val proofNew = WeakeningLeftRule( subProofNew, mainOcc.formula )
      val sequentNew = mainOcc +: sequent.map( o => proof.getDescendantInLowerSequent( o ).get )

      testCorrectness( proof, proofNew, sequentNew )

    case lkOld.WeakeningRightRule( subProof, endSequent, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val proofNew = WeakeningRightRule( subProofNew, mainOcc.formula )
      val sequentNew = sequent.map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc

      testCorrectness( proof, proofNew, sequentNew )

    case lkOld.ContractionLeftRule( subProof, endSequent, aux1Occ, aux2Occ, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val ( aux1, aux2 ) = ( sequent indexOf aux1Occ, sequent indexOf aux2Occ )
      val proofNew = ContractionLeftRule( subProofNew, aux1, aux2 )

      testCorrectness( proof, proofNew, mainOcc +: sequent.delete( aux1, aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lkOld.ContractionRightRule( subProof, endSequent, aux1Occ, aux2Occ, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val ( aux1, aux2 ) = ( sequent indexOf aux1Occ, sequent indexOf aux2Occ )
      val proofNew = ContractionRightRule( subProofNew, aux1, aux2 )

      testCorrectness( proof, proofNew, sequent.delete( aux1, aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lkOld.CutRule( leftSubProof, rightSubProof, endSequent, aux1Occ, aux2Occ ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( aux1, aux2 ) = ( leftSequent indexOf aux1Occ, rightSequent indexOf aux2Occ )
      val proofNew = CutRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

      testCorrectness( proof, proofNew, leftSequent.delete( aux1 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lkOld.NegLeftRule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val proofNew = NegLeftRule( subProofNew, aux )

      testCorrectness( proof, proofNew, mainOcc +: sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lkOld.NegRightRule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val proofNew = NegRightRule( subProofNew, aux )

      testCorrectness( proof, proofNew, sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lkOld.AndLeft1Rule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( leftConjunct, rightConjunct ) = mainOcc.formula match { case And( f, g ) => ( f, g ) }
      val proofNew_ = WeakeningLeftRule( subProofNew, rightConjunct )
      val conn1 = proofNew_.getOccConnector
      val proofNew = AndLeftRule( proofNew_, conn1.child( aux ), proofNew_.mainIndices.head )

      testCorrectness( proof, proofNew, mainOcc +: sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lkOld.AndLeft2Rule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( leftConjunct, rightConjunct ) = mainOcc.formula match { case And( f, g ) => ( f, g ) }
      val proofNew_ = WeakeningLeftRule( subProofNew, leftConjunct )
      val conn1 = proofNew_.getOccConnector
      val proofNew = AndLeftRule( proofNew_, proofNew_.mainIndices.head, conn1.child( aux ) )

      testCorrectness( proof, proofNew, mainOcc +: sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lkOld.AndRightRule( leftSubProof, rightSubProof, endSequent, aux1Occ, aux2Occ, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( aux1, aux2 ) = ( leftSequent indexOf aux1Occ, rightSequent indexOf aux2Occ )
      val proofNew = AndRightRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

      testCorrectness( proof, proofNew, ( leftSequent.delete( aux1 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) :+ mainOcc )

    case lkOld.OrLeftRule( leftSubProof, rightSubProof, endSequent, aux1Occ, aux2Occ, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( aux1, aux2 ) = ( leftSequent indexOf aux1Occ, rightSequent indexOf aux2Occ )
      val proofNew = OrLeftRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

      testCorrectness( proof, proofNew, mainOcc +: ( leftSequent.delete( aux1 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) )

    case lkOld.OrRight1Rule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( leftDisjunct, rightDisjunct ) = mainOcc.formula match { case Or( f, g ) => ( f, g ) }
      val proofNew_ = WeakeningRightRule( subProofNew, rightDisjunct )
      val conn1 = proofNew_.getOccConnector
      val proofNew = OrRightRule( proofNew_, conn1.child( aux ), proofNew_.mainIndices.head )

      testCorrectness( proof, proofNew, sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lkOld.OrRight2Rule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( leftDisjunct, rightDisjunct ) = mainOcc.formula match { case Or( f, g ) => ( f, g ) }
      val proofNew_ = WeakeningRightRule( subProofNew, leftDisjunct )
      val conn1 = proofNew_.getOccConnector
      val proofNew = OrRightRule( proofNew_, proofNew_.mainIndices.head, conn1.child( aux ) )

      testCorrectness( proof, proofNew, sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lkOld.ImpLeftRule( leftSubProof, rightSubProof, endSequent, aux1Occ, aux2Occ, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( aux1, aux2 ) = ( leftSequent indexOf aux1Occ, rightSequent indexOf aux2Occ )
      val proofNew = ImpLeftRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

      testCorrectness( proof, proofNew, mainOcc +: ( leftSequent.delete( aux1 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) )

    case lkOld.ImpRightRule( subProof, endSequent, aux1Occ, aux2Occ, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val ( impPremise, impConclusion ) = ( aux1Occ.formula, aux2Occ.formula )
      val ( aux1, aux2 ) = ( sequent indexOf aux1Occ, sequent indexOf aux2Occ )
      val proofNew = ImpRightRule( subProofNew, aux1, aux2 )

      testCorrectness( proof, proofNew, sequent.delete( aux1, aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lkOld.ForallLeftRule( subProof, endSequent, auxOcc, mainOcc, term ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( v, mat ) = mainOcc.formula match { case All( x, f ) => ( x, f ) }
      val proofNew = ForallLeftRule( subProofNew, aux, mat, term, v )

      testCorrectness( proof, proofNew, mainOcc +: sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lkOld.ForallRightRule( subProof, endSequent, auxOcc, mainOcc, eigen ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( v, mat ) = mainOcc.formula match { case All( x, f ) => ( x, f ) }
      val proofNew = ForallRightRule( subProofNew, aux, eigen, v )

      testCorrectness( proof, proofNew, sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lkOld.ExistsLeftRule( subProof, endSequent, auxOcc, mainOcc, eigen ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( v, mat ) = mainOcc.formula match { case Ex( x, f ) => ( x, f ) }
      val proofNew = ExistsLeftRule( subProofNew, aux, eigen, v )

      testCorrectness( proof, proofNew, mainOcc +: sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lkOld.ExistsRightRule( subProof, endSequent, auxOcc, mainOcc, term ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( v, mat ) = mainOcc.formula match { case Ex( x, f ) => ( x, f ) }
      val proofNew = ExistsRightRule( subProofNew, aux, mat, term, v )

      testCorrectness( proof, proofNew, sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lkOld.EquationLeft1Rule( leftSubProof, rightSubProof, endSequent, eqOcc, auxOcc, pos, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( eq, aux ) = ( leftSequent indexOf eqOcc, rightSequent indexOf auxOcc )
      val proofNew = ParamodulationLeftRule( leftSubProofNew, eq, rightSubProofNew, aux, pos.head )

      testCorrectness( proof, proofNew, ( leftSequent.delete( eq ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ Sequent( Seq( mainOcc ), Seq() ) ++ rightSequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) )

    case lkOld.EquationLeft2Rule( leftSubProof, rightSubProof, endSequent, eqOcc, auxOcc, pos, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( eq, aux ) = ( leftSequent indexOf eqOcc, rightSequent indexOf auxOcc )
      val proofNew = ParamodulationLeftRule( leftSubProofNew, eq, rightSubProofNew, aux, pos.head )

      testCorrectness( proof, proofNew, ( leftSequent.delete( eq ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ Sequent( Seq( mainOcc ), Seq() ) ++ rightSequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) )

    case lkOld.EquationRight1Rule( leftSubProof, rightSubProof, endSequent, eqOcc, auxOcc, pos, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( eq, aux ) = ( leftSequent indexOf eqOcc, rightSequent indexOf auxOcc )
      val proofNew = ParamodulationRightRule( leftSubProofNew, eq, rightSubProofNew, aux, pos.head )

      testCorrectness( proof, proofNew, ( leftSequent.delete( eq ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) :+ mainOcc )

    case lkOld.EquationRight2Rule( leftSubProof, rightSubProof, endSequent, eqOcc, auxOcc, pos, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( eq, aux ) = ( leftSequent indexOf eqOcc, rightSequent indexOf auxOcc )
      val proofNew = ParamodulationRightRule( leftSubProofNew, eq, rightSubProofNew, aux, pos.head )

      testCorrectness( proof, proofNew, ( leftSequent.delete( eq ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) :+ mainOcc )

    case lkOld.DefinitionLeftRule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val proofNew = DefinitionLeftRule( subProofNew, aux, mainOcc.formula )

      testCorrectness( proof, proofNew, mainOcc +: sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lkOld.DefinitionRightRule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val proofNew = DefinitionRightRule( subProofNew, aux, mainOcc.formula )

      testCorrectness( proof, proofNew, sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )
  }

  /**
   * Tests whether the conversion has been performed correctly. Was used for debugging.
   *
   * @param oldProof
   * @param newProof
   * @param sequent
   * @return
   */
  def testCorrectness( oldProof: lkOld.base.LKProof, newProof: LKProof, sequent: OccSequent ): ( LKProof, OccSequent ) = {
    require( oldProof.root.sizes == newProof.endSequent.sizes )
    require( newProof.endSequent.sizes == sequent.sizes )
    oldProof.root.elements.foreach { o =>
      val i = sequent indexOf o
      if ( newProof.endSequent( i ) != o.formula )
        throw new Exception( s"Old2New: Incorrect sequent for oldproof = $oldProof, newproof = $newProof, sequent = $sequent at index $i: formula should be ${o.formula}, but is ${newProof.endSequent( i )}}." )
    }

    ( newProof, sequent )
  }
}