package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.proofs.{ Ant, Suc, Sequent, Clause }
import at.logic.gapt.proofs.lk.base.{ PrincipalFormulas }
import at.logic.gapt.proofs.lkNew.OccConnector
import at.logic.gapt.proofs.occurrences.FormulaOccurrence
import at.logic.gapt.proofs.resolutionOld.robinson
import at.logic.gapt.proofs.resolutionOld._

import scala.collection.mutable

private object followOccs {
  def apply(
    upperCorrs:  Seq[Sequent[FormulaOccurrence]],
    oldLower:    OccClause,
    newOccConns: Seq[OccConnector]
  ): Sequent[FormulaOccurrence] =
    newOccConns.head.lowerSequent.indicesSequent map { newLowerIdx =>
      ( for (
        ( upperCorr, newOccConn ) <- ( upperCorrs, newOccConns ).zipped;
        oldUpperOcc <- newOccConn.parents( newLowerIdx ).map( upperCorr( _ ) );
        oldLowerOcc <- if ( newLowerIdx.isAnt ) oldLower.antecedent else oldLower.succedent;
        if oldLowerOcc.parents contains oldUpperOcc
      ) yield oldLowerOcc ).head
    }
}

object resOld2New {

  def apply( res: robinson.RobinsonResolutionProof ): ResolutionProof = {
    val memo = mutable.Map[robinson.RobinsonResolutionProof, ( ResolutionProof, Sequent[FormulaOccurrence] )]()

    def f( res: robinson.RobinsonResolutionProof, subst: Substitution ): ( ResolutionProof, Sequent[FormulaOccurrence] ) = {
      val ( resNew, corr ) = g( res )
      require( corr.elements == corr.elements.distinct )
      require( corr.toHOLClause multiSetEquals resNew.conclusion )
      Instance( resNew, FOLSubstitution( subst.map.map { case ( v: FOLVar, t: FOLTerm ) => v -> t } ) ) -> corr
    }

    def g( res: robinson.RobinsonResolutionProof ): ( ResolutionProof, Sequent[FormulaOccurrence] ) =
      memo.getOrElseUpdate( res, res match {
        case robinson.InitialClause( clause ) =>
          clause.toHOLClause match {
            case Clause( Seq(), Seq( Eq( t, s ) ) ) if t == s => ReflexivityClause( t.asInstanceOf[FOLTerm] ) -> clause
            case Clause( Seq( a ), Seq( b ) ) if a == b => TautologyClause( a.asInstanceOf[FOLAtom] ) -> clause
            case cls => InputClause( cls map { _.asInstanceOf[FOLAtom] } ) -> clause
          }
        case robinson.Factor( clause, p1, List( occs ), subst ) =>
          val ( p1New, corr1 ) = f( p1, subst )
          val ( pNew, occConn ) = Factor( p1New, occs.map( corr1 indexOf _ ) )
          pNew -> followOccs( Seq( corr1 ), res.root, Seq( occConn ) )
        case robinson.Variant( clause, p1, subst ) =>
          val ( p1New, corr1 ) = f( p1, subst )
          p1New -> followOccs( Seq( corr1 ), res.root, p1New.occConnectors )
        case robinson.Instance( clause, p1, subst ) =>
          val ( p1New, corr1 ) = f( p1, subst )
          p1New -> followOccs( Seq( corr1 ), res.root, p1New.occConnectors )
        case robinson.Resolution( clause, p1, p2, occ1, occ2, subst ) =>
          val ( p1New, corr1 ) = f( p1, subst )
          val ( p2New, corr2 ) = f( p2, subst )
          val pNew = Resolution( p1New, corr1 indexOf occ1, p2New, corr2 indexOf occ2 )
          pNew -> followOccs( Seq( corr1, corr2 ), res.root, pNew.occConnectors )
        case robinson.Paramodulation( clause, p1, p2, occ1, occ2, main, subst ) =>
          val ( p1New, corr1 ) = f( p1, subst )
          val ( p2New, corr2 ) = f( p2, subst )
          val pNew = Paramodulation( p1New, corr1 indexOf occ1, p2New, corr2 indexOf occ2, main.formula.asInstanceOf[FOLAtom] )
          pNew -> followOccs( Seq( corr1, corr2 ), res.root, pNew.occConnectors )
      } )

    g( res )._1
  }

}

object resNew2Old {

  def apply( res: ResolutionProof ): robinson.RobinsonResolutionProof = {
    val memo = mutable.Map[ResolutionProof, ( robinson.RobinsonResolutionProof, Sequent[FormulaOccurrence] )]()

    def check( res: ResolutionProof, ret: ( robinson.RobinsonResolutionProof, Sequent[FormulaOccurrence] ) ): ( robinson.RobinsonResolutionProof, Sequent[FormulaOccurrence] ) = {
      val ( oldRes, corr ) = ret
      require( corr == corr.distinct )
      require( corr.toHOLClause multiSetEquals res.conclusion )
      require( corr multiSetEquals oldRes.root )
      ret
    }

    def f( res: ResolutionProof ): ( robinson.RobinsonResolutionProof, Sequent[FormulaOccurrence] ) =
      check( res, memo.getOrElseUpdate( res, res match {
        case _: InitialClause =>
          val resOld = robinson.InitialClause( res.conclusion )
          resOld -> resOld.root
        case Instance( subProof, subst ) =>
          val ( subProofOld, corr ) = f( subProof )
          val resOld = robinson.Instance( subProofOld, subst )
          resOld -> followOccs( Seq( corr ), resOld.root, res.occConnectors )
        case Factor( subProof, idx1, idx2 ) =>
          val ( subProofOld, corr ) = f( subProof )
          val resOld = robinson.Factor( subProofOld, corr( idx1 ), Seq( corr( idx2 ) ), FOLSubstitution() )
          resOld -> followOccs( Seq( corr ), resOld.root, res.occConnectors )
        case Resolution( subProof1, idx1 @ Suc( _ ), subProof2, idx2 ) =>
          val ( subProofOld1, corr1 ) = f( subProof1 )
          val ( subProofOld2, corr2 ) = f( subProof2 )
          val resOld = robinson.Resolution( subProofOld1, subProofOld2, corr1( idx1 ), corr2( idx2 ), FOLSubstitution() )
          resOld -> followOccs( Seq( corr1, corr2 ), resOld.root, res.occConnectors )
        case Resolution( subProof2, idx2 @ Ant( _ ), subProof1, idx1 ) =>
          val ( subProofOld1, corr1 ) = f( subProof1 )
          val ( subProofOld2, corr2 ) = f( subProof2 )
          val resOld = robinson.Resolution( subProofOld1, subProofOld2, corr1( idx1 ), corr2( idx2 ), FOLSubstitution() )
          resOld -> followOccs( Seq( corr1, corr2 ), resOld.root, res.occConnectors.reverse )
        case Paramodulation( subProof1, equation, subProof2, literal, positions, leftToRight ) =>
          val ( subProofOld1, corr1 ) = f( subProof1 )
          val ( subProofOld2, corr2 ) = f( subProof2 )
          val resOld = robinson.Paramodulation( subProofOld1, subProofOld2, corr1( equation ), corr2( literal ), res.mainFormulas.head, FOLSubstitution() )
          resOld -> followOccs( Seq( corr1, corr2 ), resOld.root, res.occConnectors )
      } ) )

    f( res )._1
  }

}