package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._
import at.logic.gapt.proofs.occurrences.FormulaOccurrence
import at.logic.gapt.proofs.{ SequentIndex, Sequent, Ant, lk }
import at.logic.gapt.proofs.lk.base.OccSequent
import at.logic.gapt.proofs.lk.base.RichOccSequent

import scala.collection.immutable.HashMap

object lkNew2Old {
  def apply( proof: LKProof ): lk.base.LKProof = apply_( proof )._1

  private def apply_( proof: LKProof ): ( lk.base.LKProof, OccSequent ) = proof match {
    case LogicalAxiom( atom ) =>
      val ax = lk.Axiom( atom )
      ( ax, ax.root )

    case ReflexivityAxiom( t ) =>
      val ax = lk.Axiom( Seq(), Seq( Eq( t, t ) ) )
      ( ax, ax.root )

    case TopAxiom =>
      val ax = lk.Axiom( Seq(), Seq( Top() ) )
      ( ax, ax.root )

    case BottomAxiom =>
      val ax = lk.Axiom( Seq( Bottom() ), Seq() )
      ( ax, ax.root )

    case ArbitraryAxiom( sequent ) =>
      val ax = lk.Axiom( sequent )
      ( ax, ax.root )

    case WeakeningLeftRule( subProof, formula ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.WeakeningLeftRule( subProofOld, formula )

      ( proofOld, proofOld.prin.head +: sequent.map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case WeakeningRightRule( subProof, formula ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.WeakeningRightRule( subProofOld, formula )

      ( proofOld, sequent.map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case ContractionLeftRule( subProof, aux1, aux2 ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.ContractionLeftRule( subProofOld, sequent( aux1 ), sequent( aux2 ) )

      ( proofOld, proofOld.prin.head +: sequent.delete( aux1, aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case ContractionRightRule( subProof, aux1, aux2 ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.ContractionRightRule( subProofOld, sequent( aux1 ), sequent( aux2 ) )

      ( proofOld, sequent.delete( aux1, aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofOld, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofOld, rightSequent ) = apply_( rightSubProof )
      val proofOld = lk.CutRule( leftSubProofOld, rightSubProofOld, leftSequent( aux1 ), rightSequent( aux2 ) )

      ( proofOld, leftSequent.delete( aux1 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case NegLeftRule( subProof, aux ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.NegLeftRule( subProofOld, sequent( aux ) )

      ( proofOld, proofOld.prin.head +: sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case NegRightRule( subProof, aux ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.NegRightRule( subProofOld, sequent( aux ) )

      ( proofOld, sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case AndLeftRule( subProof, aux1, aux2 ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.AndLeftRule( subProofOld, sequent( aux1 ), sequent( aux2 ) )

      ( proofOld, proofOld.prin.head +: sequent.delete( aux1, aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofOld, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofOld, rightSequent ) = apply_( rightSubProof )
      val proofOld = lk.AndRightRule( leftSubProofOld, rightSubProofOld, leftSequent( aux1 ), rightSequent( aux2 ) )

      ( proofOld, ( leftSequent.delete( aux1 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ) :+ proofOld.prin.head )

    case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofOld, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofOld, rightSequent ) = apply_( rightSubProof )
      val proofOld = lk.OrLeftRule( leftSubProofOld, rightSubProofOld, leftSequent( aux1 ), rightSequent( aux2 ) )

      ( proofOld, proofOld.prin.head +: ( leftSequent.delete( aux1 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ) )

    case OrRightRule( subProof, aux1, aux2 ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.OrRightRule( subProofOld, sequent( aux1 ), sequent( aux2 ) )

      ( proofOld, sequent.delete( aux1, aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val ( leftSubProofOld, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofOld, rightSequent ) = apply_( rightSubProof )
      val proofOld = lk.ImpLeftRule( leftSubProofOld, rightSubProofOld, leftSequent( aux1 ), rightSequent( aux2 ) )

      ( proofOld, proofOld.prin.head +: ( leftSequent.delete( aux1 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ) )

    case ImpRightRule( subProof, aux1, aux2 ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.ImpRightRule( subProofOld, sequent( aux1 ), sequent( aux2 ) )

      ( proofOld, sequent.delete( aux1, aux2 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case ForallLeftRule( subProof, aux, f, t, v ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.ForallLeftRule( subProofOld, sequent( aux ), All( v, f ), t )

      ( proofOld, proofOld.prin.head +: sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case ForallRightRule( subProof, aux, eigen, quant ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.ForallRightRule( subProofOld, sequent( aux ), proof.mainFormulas.head, eigen )

      ( proofOld, sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case ExistsLeftRule( subProof, aux, eigen, quant ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.ExistsLeftRule( subProofOld, sequent( aux ), proof.mainFormulas.head, eigen )

      ( proofOld, proofOld.prin.head +: sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) )

    case ExistsRightRule( subProof, aux, f, t, v ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val proofOld = lk.ExistsRightRule( subProofOld, sequent( aux ), All( v, f ), t )

      ( proofOld, sequent.delete( aux ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )

    case EqualityLeftRule( subProof, eq, aux, pos ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val equation = proof.auxFormulas.head.head
      val ax = lk.Axiom( equation )
      val proofOld_ = lk.EquationLeftRule( ax, subProofOld, ax.root.succedent.head, sequent( aux ), pos )
      val proofOld = lk.ContractionLeftRule( proofOld_, proofOld_.getDescendantInLowerSequent( ax.root.antecedent.head ).get, proofOld_.getDescendantInLowerSequent( sequent( eq ) ).get )

      val newAnt = for ( i <- sequent.antecedent.indices.map( j => Ant( j ) ) ) yield {
        if ( i == eq )
          proofOld.getDescendantInLowerSequent( ax.root.succedent.head ).get
        else
          proofOld.getDescendantInLowerSequent( sequent( i ) ).get
      }

      val newSuc = for ( i <- sequent.succedent ) yield proofOld.getDescendantInLowerSequent( i ).get

      ( proofOld, proofOld.prin.head +: Sequent( newAnt, newSuc ).delete( aux ) )

    case EqualityRightRule( subProof, eq, aux, pos ) =>
      val ( subProofOld, sequent ) = apply_( subProof )
      val equation = proof.auxFormulas.head.head
      val ax = lk.Axiom( equation )
      val proofOld_ = lk.EquationRightRule( ax, subProofOld, ax.root.succedent.head, sequent( aux ), pos )
      val proofOld = lk.ContractionLeftRule( proofOld_, proofOld_.getDescendantInLowerSequent( ax.root.antecedent.head ).get, proofOld_.getDescendantInLowerSequent( sequent( eq ) ).get )

      val newAnt = for ( i <- sequent.antecedent.indices.map( j => Ant( j ) ) ) yield {
        if ( i == eq )
          proofOld.getDescendantInLowerSequent( ax.root.succedent.head ).get
        else
          proofOld.getDescendantInLowerSequent( sequent( i ) ).get
      }

      val newSuc = for ( i <- sequent.succedent ) yield proofOld.getDescendantInLowerSequent( i ).get

      ( proofOld, proofOld.prin.head +: Sequent( newAnt, newSuc ).delete( aux ) )

    case InductionRule( leftSubProof, aux1, rightSubProof, aux2, aux3, term ) =>
      val ( leftSubProofOld, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofOld, rightSequent ) = apply_( rightSubProof )
      val proofOld = lk.InductionRule( leftSubProofOld, rightSubProofOld, leftSequent( aux1 ), rightSequent( aux2 ), rightSequent( aux3 ), term )

      ( proofOld, leftSequent.delete( aux1 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2, aux3 ).map( o => proofOld.getDescendantInLowerSequent( o ).get ) :+ proofOld.prin.head )
  }
}

object lkOld2New {

  def apply( proof: lk.base.LKProof ): LKProof = apply_( proof )._1

  private def apply_( proof: lk.base.LKProof ): ( LKProof, OccSequent ) = proof match {
    case lk.Axiom( sequent ) =>
      ( Axiom( sequent.toHOLSequent ), sequent )

    case lk.WeakeningLeftRule( subProof, _, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val proofNew = WeakeningLeftRule( subProofNew, mainOcc.formula )

      ( proofNew, mainOcc +: sequent.map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lk.WeakeningRightRule( subProof, endSequent, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val proofNew = WeakeningRightRule( subProofNew, mainOcc.formula )

      ( proofNew, sequent.map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lk.ContractionLeftRule( subProof, endSequent, aux1Occ, aux2Occ, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val ( aux1, aux2 ) = ( sequent indexOf aux1Occ, sequent indexOf aux2Occ )
      val proofNew = ContractionLeftRule( subProofNew, aux1, aux2 )

      ( proofNew, mainOcc +: sequent.delete( aux1, aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lk.ContractionRightRule( subProof, endSequent, aux1Occ, aux2Occ, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val ( aux1, aux2 ) = ( sequent indexOf aux1Occ, sequent indexOf aux2Occ )
      val proofNew = ContractionRightRule( subProofNew, aux1, aux2 )

      ( proofNew, sequent.delete( aux1, aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lk.CutRule( leftSubProof, rightSubProof, endSequent, aux1Occ, aux2Occ ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( aux1, aux2 ) = ( leftSequent indexOf aux1Occ, rightSequent indexOf aux2Occ )
      val proofNew = CutRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

      ( proofNew, leftSequent.delete( aux1 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lk.NegLeftRule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val proofNew = NegLeftRule( subProofNew, aux )

      ( proofNew, mainOcc +: sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lk.NegRightRule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val proofNew = NegRightRule( subProofNew, aux )

      ( proofNew, sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lk.AndLeft1Rule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( leftConjunct, rightConjunct ) = mainOcc.formula match { case And( f, g ) => ( f, g ) }
      val proofNew_ = WeakeningLeftRule( subProofNew, rightConjunct )
      val proofNew = AndLeftRule( proofNew_, aux + 1, Ant( 0 ) )

      ( proofNew, mainOcc +: sequent.delete( Ant( 0 ), aux + 1 ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lk.AndLeft2Rule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( leftConjunct, rightConjunct ) = mainOcc.formula match { case And( f, g ) => ( f, g ) }
      val proofNew_ = WeakeningLeftRule( subProofNew, leftConjunct )
      val proofNew = AndLeftRule( proofNew_, Ant( 0 ), aux + 1 )

      ( proofNew, mainOcc +: sequent.delete( Ant( 0 ), aux + 1 ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lk.AndRightRule( leftSubProof, rightSubProof, endSequent, aux1Occ, aux2Occ, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( aux1, aux2 ) = ( leftSequent indexOf aux1Occ, rightSequent indexOf aux2Occ )
      val proofNew = AndRightRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

      ( proofNew, ( leftSequent.delete( aux1 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) :+ mainOcc )

    case lk.OrLeftRule( leftSubProof, rightSubProof, endSequent, aux1Occ, aux2Occ, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( aux1, aux2 ) = ( leftSequent indexOf aux1Occ, rightSequent indexOf aux2Occ )
      val proofNew = OrLeftRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

      ( proofNew, mainOcc +: ( leftSequent.delete( aux1 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) )

    case lk.OrRight1Rule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( leftDisjunct, rightDisjunct ) = mainOcc.formula match { case Or( f, g ) => ( f, g ) }
      val proofNew_ = WeakeningRightRule( subProofNew, rightDisjunct )
      val proofNew = OrRightRule( proofNew_, aux, proofNew_.mainIndices.head )

      ( proofNew, sequent.delete( proofNew_.mainIndices.head, aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lk.OrRight2Rule( subProof, endSequent, auxOcc, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( leftDisjunct, rightDisjunct ) = mainOcc.formula match { case Or( f, g ) => ( f, g ) }
      val proofNew_ = WeakeningRightRule( subProofNew, leftDisjunct )
      val proofNew = OrRightRule( proofNew_, proofNew_.mainIndices.head, aux )

      ( proofNew, sequent.delete( proofNew_.mainIndices.head, aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lk.ImpLeftRule( leftSubProof, rightSubProof, endSequent, aux1Occ, aux2Occ, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( aux1, aux2 ) = ( leftSequent indexOf aux1Occ, rightSequent indexOf aux2Occ )
      val proofNew = ImpLeftRule( leftSubProofNew, aux1, rightSubProofNew, aux2 )

      ( proofNew, mainOcc +: ( leftSequent.delete( aux1 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) )

    case lk.ImpRightRule( subProof, endSequent, aux1Occ, aux2Occ, mainOcc ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val ( impPremise, impConclusion ) = ( aux1Occ.formula, aux2Occ.formula )
      val ( aux1, aux2 ) = ( sequent indexOf aux1Occ, sequent indexOf aux2Occ )
      val proofNew = ImpRightRule( subProofNew, aux1, aux2 )

      ( proofNew, sequent.delete( aux1, aux2 ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lk.ForallLeftRule( subProof, endSequent, auxOcc, mainOcc, term ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( v, mat ) = mainOcc.formula match { case All( x, f ) => ( x, f ) }
      val proofNew = ForallLeftRule( subProofNew, aux, mat, term, v )

      ( proofNew, mainOcc +: sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lk.ForallRightRule( subProof, endSequent, auxOcc, mainOcc, eigen ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( v, mat ) = mainOcc.formula match { case All( x, f ) => ( x, f ) }
      val proofNew = ForallRightRule( subProofNew, aux, eigen, v )

      ( proofNew, sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lk.ExistsLeftRule( subProof, endSequent, auxOcc, mainOcc, eigen ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( v, mat ) = mainOcc.formula match { case Ex( x, f ) => ( x, f ) }
      val proofNew = ExistsLeftRule( subProofNew, aux, eigen, v )

      ( proofNew, mainOcc +: sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) )

    case lk.ExistsRightRule( subProof, endSequent, auxOcc, mainOcc, term ) =>
      val ( subProofNew, sequent ) = apply_( subProof )
      val aux = sequent indexOf auxOcc
      val ( v, mat ) = mainOcc.formula match { case Ex( x, f ) => ( x, f ) }
      val proofNew = ExistsRightRule( subProofNew, aux, mat, term, v )

      ( proofNew, sequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) :+ mainOcc )

    case lk.EquationLeft1Rule( leftSubProof, rightSubProof, endSequent, eqOcc, auxOcc, pos, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( eq, aux ) = ( leftSequent indexOf eqOcc, rightSequent indexOf auxOcc )
      val proofNew = ParamodulationLeftRule( leftSubProofNew, eq, rightSubProofNew, aux, pos.head )

      ( proofNew, mainOcc +: ( leftSequent.delete( eq ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) )

    case lk.EquationLeft2Rule( leftSubProof, rightSubProof, endSequent, eqOcc, auxOcc, pos, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( eq, aux ) = ( leftSequent indexOf eqOcc, rightSequent indexOf auxOcc )
      val proofNew = ParamodulationLeftRule( leftSubProofNew, eq, rightSubProofNew, aux, pos.head )

      ( proofNew, mainOcc +: ( leftSequent.delete( eq ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) )

    case lk.EquationRight1Rule( leftSubProof, rightSubProof, endSequent, eqOcc, auxOcc, pos, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( eq, aux ) = ( leftSequent indexOf eqOcc, rightSequent indexOf auxOcc )
      val proofNew = ParamodulationRightRule( leftSubProofNew, eq, rightSubProofNew, aux, pos.head )

      ( proofNew, ( leftSequent.delete( eq ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) :+ mainOcc )

    case lk.EquationRight2Rule( leftSubProof, rightSubProof, endSequent, eqOcc, auxOcc, pos, mainOcc ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( eq, aux ) = ( leftSequent indexOf eqOcc, rightSequent indexOf auxOcc )
      val proofNew = ParamodulationRightRule( leftSubProofNew, eq, rightSubProofNew, aux, pos.head )

      ( proofNew, ( leftSequent.delete( eq ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) :+ mainOcc )

    case lk.InductionRule( leftSubProof, rightSubProof, endSequent, aux1Occ, aux2Occ, aux3Occ, mainOcc, term ) =>
      val ( leftSubProofNew, leftSequent ) = apply_( leftSubProof )
      val ( rightSubProofNew, rightSequent ) = apply_( rightSubProof )
      val ( aux1, aux2, aux3 ) = ( leftSequent indexOf aux1Occ, rightSequent indexOf aux2Occ, rightSequent indexOf aux3Occ )
      val proofNew = InductionRule( leftSubProofNew, aux1, rightSubProofNew, aux2, aux3, term )

      ( proofNew, ( leftSequent.delete( aux1 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ++ rightSequent.delete( aux2, aux3 ).map( o => proof.getDescendantInLowerSequent( o ).get ) ) :+ mainOcc )
  }
}