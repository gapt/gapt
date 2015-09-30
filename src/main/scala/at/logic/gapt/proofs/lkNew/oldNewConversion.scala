package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr.{ All, Bottom, Top, Eq }
import at.logic.gapt.proofs.occurrences.FormulaOccurrence
import at.logic.gapt.proofs.{ Sequent, Ant, lk }
import at.logic.gapt.proofs.lk.base.OccSequent

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