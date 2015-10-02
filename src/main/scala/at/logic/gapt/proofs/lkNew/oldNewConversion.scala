package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._
import at.logic.gapt.proofs.occurrences.FormulaOccurrence
import at.logic.gapt.proofs.{ SequentIndex, Sequent, Ant, lk }
import at.logic.gapt.proofs.lk.base.{ PrincipalFormulas, OccSequent, RichOccSequent }

import scala.collection.immutable.HashMap

object lkNew2Old {
  def apply( proof: LKProof ): lk.base.LKProof = apply_( proof )._1

  private def apply_( proof: LKProof ): ( lk.base.LKProof, OccSequent ) = proof match {
    case LogicalAxiom( atom ) =>
      val ax = lk.Axiom( atom )
      testCorrectness( ax, proof, ax.root )

    case ReflexivityAxiom( t ) =>
      val ax = lk.Axiom( Seq(), Seq( Eq( t, t ) ) )
      testCorrectness( ax, proof, ax.root )

    case TopAxiom =>
      val ax = lk.Axiom( Seq(), Seq( Top() ) )
      testCorrectness( ax, proof, ax.root )

    case BottomAxiom =>
      val ax = lk.Axiom( Seq( Bottom() ), Seq() )
      testCorrectness( ax, proof, ax.root )

    case ArbitraryAxiom( sequent ) =>
      val ax = lk.Axiom( sequent )
      testCorrectness( ax, proof, ax.root )

    case WeakeningLeftRule( subProof, formula ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.WeakeningLeftRule( subProofOld, formula )

      testCorrectness( proofOld, proof, proofOld.prin.head +: sequent.map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case WeakeningRightRule( subProof, formula ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.WeakeningRightRule( subProofOld, formula )

      testCorrectness( proofOld, proof, sequent.map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case ContractionLeftRule( subProof, aux1, aux2 ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.ContractionLeftRule( subProofOld, sequent( aux1 ), sequent( aux2 ) )

      testCorrectness( proofOld, proof, proofOld.prin.head +: sequent.delete( aux1, aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case ContractionRightRule( subProof, aux1, aux2 ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.ContractionRightRule( subProofOld, sequent( aux1 ), sequent( aux2 ) )

      testCorrectness( proofOld, proof, sequent.delete( aux1, aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofOld, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofOld, rightSequent ) = apply_( rightSubProof )
      val proofOld = lk.CutRule( leftSubProofOld, rightSubProofOld, leftSequent( aux1 ), rightSequent( aux2 ) )

      testCorrectness( proofOld, proof, leftSequent.delete( aux1 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case NegLeftRule( subProof, aux ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.NegLeftRule( subProofOld, sequent( aux ) )

      testCorrectness( proofOld, proof, proofOld.prin.head +: sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case NegRightRule( subProof, aux ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.NegRightRule( subProofOld, sequent( aux ) )

      testCorrectness( proofOld, proof, sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case AndLeftRule( subProof, aux1, aux2 ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.AndLeftRule( subProofOld, sequent( aux1 ), sequent( aux2 ) )

      testCorrectness( proofOld, proof, proofOld.prin.head +: sequent.delete( aux1, aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofOld, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofOld, rightSequent ) = apply_( rightSubProof )
      val proofOld = lk.AndRightRule( leftSubProofOld, rightSubProofOld, leftSequent( aux1 ), rightSequent( aux2 ) )

      testCorrectness( proofOld, proof, ( leftSequent.delete( aux1 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ) :+ proofOld.prin.head )

    case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofOld, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofOld, rightSequent ) = apply_( rightSubProof )
      val proofOld = lk.OrLeftRule( leftSubProofOld, rightSubProofOld, leftSequent( aux1 ), rightSequent( aux2 ) )

      testCorrectness( proofOld, proof, proofOld.prin.head +: ( leftSequent.delete( aux1 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ) )

    case OrRightRule( subProof, aux1, aux2 ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.OrRightRule( subProofOld, sequent( aux1 ), sequent( aux2 ) )

      testCorrectness( proofOld, proof, sequent.delete( aux1, aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofOld, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofOld, rightSequent ) = apply_( rightSubProof )
      val proofOld = lk.ImpLeftRule( leftSubProofOld, rightSubProofOld, leftSequent( aux1 ), rightSequent( aux2 ) )

      testCorrectness( proofOld, proof, proofOld.prin.head +: ( leftSequent.delete( aux1 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ) )

    case ImpRightRule( subProof, aux1, aux2 ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.ImpRightRule( subProofOld, sequent( aux1 ), sequent( aux2 ) )

      testCorrectness( proofOld, proof, sequent.delete( aux1, aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case ForallLeftRule( subProof, aux, f, t, v ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.ForallLeftRule( subProofOld, sequent( aux ), All( v, f ), t )

      testCorrectness( proofOld, proof, proofOld.prin.head +: sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case ForallRightRule( subProof, aux, eigen, quant ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.ForallRightRule( subProofOld, sequent( aux ), proof.mainFormulas.head, eigen )

      testCorrectness( proofOld, proof, sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.asInstanceOf[PrincipalFormulas].prin.head )

    case ExistsLeftRule( subProof, aux, eigen, quant ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.ExistsLeftRule( subProofOld, sequent( aux ), proof.mainFormulas.head, eigen )

      testCorrectness( proofOld, proof, proofOld.asInstanceOf[PrincipalFormulas].prin.head +: sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case ExistsRightRule( subProof, aux, f, t, v ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.ExistsRightRule( subProofOld, sequent( aux ), Ex( v, f ), t )

      testCorrectness( proofOld, proof, sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case EqualityLeftRule( subProof, eq, aux, pos ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val equation = proof.auxFormulas.head.head
      val ax = lk.Axiom( equation )
      val proofOld_ = lk.EquationLeftRule( ax, subProofOld, ax.root.succedent.head, sequent( aux ), pos )
      val proofOld = lk.ContractionLeftRule( proofOld_, proofOld_.getDescendantInLowerSequent( ax.root.antecedent.head ).get, proofOld_.getDescendantInLowerSequent( sequent( eq ) ).get )

      val mainOcc = proofOld.getDescendantInLowerSequent( proofOld_.prin.head ).get
      testCorrectness( proofOld, proof, mainOcc +: sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case EqualityRightRule( subProof, eq, aux, pos ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val equation = proof.auxFormulas.head.head
      val ax = lk.Axiom( equation )
      val proofOld_ = lk.EquationRightRule( ax, subProofOld, ax.root.succedent.head, sequent( aux ), pos )
      val proofOld = lk.ContractionLeftRule( proofOld_, proofOld_.getDescendantInLowerSequent( ax.root.antecedent.head ).get, proofOld_.getDescendantInLowerSequent( sequent( eq ) ).get )

      val mainOcc = proofOld.getDescendantInLowerSequent( proofOld_.prin.head ).get
      testCorrectness( proofOld, proof, sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case InductionRule( leftSubProof, aux1, rightSubProof, aux2, aux3, term ) =>
      val ( leftSubProofOld, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofOld, rightSequent ) = apply_( rightSubProof )
      val proofOld = lk.InductionRule( leftSubProofOld, rightSubProofOld, leftSequent( aux1 ), rightSequent( aux2 ), rightSequent( aux3 ), term )

      testCorrectness( proofOld, proof, leftSequent.delete( aux1 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2, aux3 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )
  }

  def testCorrectness( oldProof: lk.base.LKProof, newProof: LKProof, sequent: OccSequent ): ( lk.base.LKProof, OccSequent ) = {
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

object lkOld2New {

  def apply( proof: lk.base.LKProof ): LKProof = apply_( proof )._1

  private def apply_( proof: lk.base.LKProof ): ( LKProof, OccSequent ) = proof match {
    case lk.Axiom( sequent ) =>
      val proofNew = Axiom( sequent.toHOLSequent )

      testCorrectness( proof, proofNew, sequent )

    case lk.WeakeningLeftRule( subProof, _, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val proofNew = WeakeningLeftRule( subProofNew, mainOcc.formula )
      val sequentNew = mainOcc +: sequent.map( o => proof.getDescendantInLowerSequent( o ).get )

      testCorrectness( proof, proofNew, sequentNew )

    case lk.WeakeningRightRule( subProof, endSequent, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val proofNew = WeakeningRightRule( subProofNew, mainOcc.formula )
      val sequentNew = sequent.map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc

      testCorrectness( proof, proofNew, sequentNew )

    case lk.ContractionLeftRule( subProof, endSequent, aux1Occ, aux2Occ, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val ( aux1, aux2 ) = ( sequent indexOf aux1Occ, sequent indexOf aux2Occ )
      val proofNew = ContractionLeftRule( subProofNew, aux1, aux2 )

      testCorrectness( proof, proofNew, mainOcc +: sequent.delete( aux1, aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lk.ContractionRightRule( subProof, endSequent, aux1Occ, aux2Occ, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val ( aux1, aux2 ) = ( sequent indexOf aux1Occ, sequent indexOf aux2Occ )
      val proofNew = ContractionRightRule( subProofNew, aux1, aux2 )

      testCorrectness( proof, proofNew, sequent.delete( aux1, aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lk.CutRule( leftSubProof, rightSubProof, endSequent, aux1Occ, aux2Occ ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( aux1, aux2 ) = ( leftSequent indexOf aux1Occ, rightSequent indexOf aux2Occ )
      val proofNew = CutRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

      testCorrectness( proof, proofNew, leftSequent.delete( aux1 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lk.NegLeftRule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val proofNew = NegLeftRule( subProofNew, aux )

      testCorrectness( proof, proofNew, mainOcc +: sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lk.NegRightRule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val proofNew = NegRightRule( subProofNew, aux )

      testCorrectness( proof, proofNew, sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lk.AndLeft1Rule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( leftConjunct, rightConjunct ) = mainOcc.formula match { case And( f, g ) => ( f, g ) }
      val proofNew_ = WeakeningLeftRule( subProofNew, rightConjunct )
      val conn1 = proofNew_.getOccConnector
      val proofNew = AndLeftRule( proofNew_, conn1.children( aux ).head, proofNew_.mainIndices.head )

      testCorrectness( proof, proofNew, mainOcc +: sequent.delete( proofNew.auxIndices.head: _* ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lk.AndLeft2Rule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( leftConjunct, rightConjunct ) = mainOcc.formula match { case And( f, g ) => ( f, g ) }
      val proofNew_ = WeakeningLeftRule( subProofNew, leftConjunct )
      val conn1 = proofNew_.getOccConnector
      val proofNew = AndLeftRule( proofNew_, proofNew_.mainIndices.head, conn1.children( aux ).head )

      testCorrectness( proof, proofNew, mainOcc +: sequent.delete( proofNew.auxIndices.head: _* ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lk.AndRightRule( leftSubProof, rightSubProof, endSequent, aux1Occ, aux2Occ, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( aux1, aux2 ) = ( leftSequent indexOf aux1Occ, rightSequent indexOf aux2Occ )
      val proofNew = AndRightRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

      testCorrectness( proof, proofNew, ( leftSequent.delete( aux1 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) :+ mainOcc )

    case lk.OrLeftRule( leftSubProof, rightSubProof, endSequent, aux1Occ, aux2Occ, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( aux1, aux2 ) = ( leftSequent indexOf aux1Occ, rightSequent indexOf aux2Occ )
      val proofNew = OrLeftRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

      testCorrectness( proof, proofNew, mainOcc +: ( leftSequent.delete( aux1 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) )

    case lk.OrRight1Rule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( leftDisjunct, rightDisjunct ) = mainOcc.formula match { case Or( f, g ) => ( f, g ) }
      val proofNew_ = WeakeningRightRule( subProofNew, rightDisjunct )
      val conn1 = proofNew_.getOccConnector
      val proofNew = OrRightRule( proofNew_, conn1.children( aux ).head, proofNew_.mainIndices.head )

      testCorrectness( proof, proofNew, sequent.delete( proofNew.auxIndices.head: _* ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lk.OrRight2Rule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( leftDisjunct, rightDisjunct ) = mainOcc.formula match { case Or( f, g ) => ( f, g ) }
      val proofNew_ = WeakeningRightRule( subProofNew, leftDisjunct )
      val conn1 = proofNew_.getOccConnector
      val proofNew = OrRightRule( proofNew_, proofNew_.mainIndices.head, conn1.children( aux ).head )

      testCorrectness( proof, proofNew, sequent.delete( proofNew.auxIndices.head: _* ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lk.ImpLeftRule( leftSubProof, rightSubProof, endSequent, aux1Occ, aux2Occ, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( aux1, aux2 ) = ( leftSequent indexOf aux1Occ, rightSequent indexOf aux2Occ )
      val proofNew = ImpLeftRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

      testCorrectness( proof, proofNew, mainOcc +: ( leftSequent.delete( aux1 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) )

    case lk.ImpRightRule( subProof, endSequent, aux1Occ, aux2Occ, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val ( impPremise, impConclusion ) = ( aux1Occ.formula, aux2Occ.formula )
      val ( aux1, aux2 ) = ( sequent indexOf aux1Occ, sequent indexOf aux2Occ )
      val proofNew = ImpRightRule( subProofNew, aux1, aux2 )

      testCorrectness( proof, proofNew, sequent.delete( aux1, aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lk.ForallLeftRule( subProof, endSequent, auxOcc, mainOcc, term ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( v, mat ) = mainOcc.formula match { case All( x, f ) => ( x, f ) }
      val proofNew = ForallLeftRule( subProofNew, aux, mat, term, v )

      testCorrectness( proof, proofNew, mainOcc +: sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lk.ForallRightRule( subProof, endSequent, auxOcc, mainOcc, eigen ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( v, mat ) = mainOcc.formula match { case All( x, f ) => ( x, f ) }
      val proofNew = ForallRightRule( subProofNew, aux, eigen, v )

      testCorrectness( proof, proofNew, sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lk.ExistsLeftRule( subProof, endSequent, auxOcc, mainOcc, eigen ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( v, mat ) = mainOcc.formula match { case Ex( x, f ) => ( x, f ) }
      val proofNew = ExistsLeftRule( subProofNew, aux, eigen, v )

      testCorrectness( proof, proofNew, mainOcc +: sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lk.ExistsRightRule( subProof, endSequent, auxOcc, mainOcc, term ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( v, mat ) = mainOcc.formula match { case Ex( x, f ) => ( x, f ) }
      val proofNew = ExistsRightRule( subProofNew, aux, mat, term, v )

      testCorrectness( proof, proofNew, sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lk.EquationLeft1Rule( leftSubProof, rightSubProof, endSequent, eqOcc, auxOcc, pos, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( eq, aux ) = ( leftSequent indexOf eqOcc, rightSequent indexOf auxOcc )
      val proofNew = ParamodulationLeftRule( leftSubProofNew, eq, rightSubProofNew, aux, pos.head )

      testCorrectness( proof, proofNew, ( leftSequent.delete( eq ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ Sequent( Seq( mainOcc ), Seq() ) ++ rightSequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) )

    case lk.EquationLeft2Rule( leftSubProof, rightSubProof, endSequent, eqOcc, auxOcc, pos, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( eq, aux ) = ( leftSequent indexOf eqOcc, rightSequent indexOf auxOcc )
      val proofNew = ParamodulationLeftRule( leftSubProofNew, eq, rightSubProofNew, aux, pos.head )

      testCorrectness( proof, proofNew, ( leftSequent.delete( eq ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ Sequent( Seq( mainOcc ), Seq() ) ++ rightSequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) )

    case lk.EquationRight1Rule( leftSubProof, rightSubProof, endSequent, eqOcc, auxOcc, pos, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( eq, aux ) = ( leftSequent indexOf eqOcc, rightSequent indexOf auxOcc )
      val proofNew = ParamodulationRightRule( leftSubProofNew, eq, rightSubProofNew, aux, pos.head )

      testCorrectness( proof, proofNew, ( leftSequent.delete( eq ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) :+ mainOcc )

    case lk.EquationRight2Rule( leftSubProof, rightSubProof, endSequent, eqOcc, auxOcc, pos, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( eq, aux ) = ( leftSequent indexOf eqOcc, rightSequent indexOf auxOcc )
      val proofNew = ParamodulationRightRule( leftSubProofNew, eq, rightSubProofNew, aux, pos.head )

      testCorrectness( proof, proofNew, ( leftSequent.delete( eq ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) :+ mainOcc )

    case lk.InductionRule( leftSubProof, rightSubProof, endSequent, aux1Occ, aux2Occ, aux3Occ, mainOcc, term ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( aux1, aux2, aux3 ) = ( leftSequent indexOf aux1Occ, rightSequent indexOf aux2Occ, rightSequent indexOf aux3Occ )
      val proofNew = InductionRule( leftSubProofNew, aux1, rightSubProofNew, aux2, aux3, term )

      testCorrectness( proof, proofNew, ( leftSequent.delete( aux1 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2, aux3 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) :+ mainOcc )
  }

  def testCorrectness( oldProof: lk.base.LKProof, newProof: LKProof, sequent: OccSequent ): ( LKProof, OccSequent ) = {
    oldProof.root.elements.foreach { o =>
      val i = sequent indexOf o
      if ( newProof.endSequent( i ) != o.formula )
        throw new Exception( s"Old2New: Incorrect sequent for oldproof = $oldProof, newproof = $newProof, sequent = $sequent at index $i: formula should be ${o.formula}, but is ${newProof.endSequent( i )}}." )
    }

    ( newProof, sequent )
  }
}