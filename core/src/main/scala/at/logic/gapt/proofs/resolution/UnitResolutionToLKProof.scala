package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr.{ Eq, HOLFormula }
import at.logic.gapt.proofs.{ Sequent, Suc }
import at.logic.gapt.proofs.lk._

object UnitResolutionToLKProof {

  def apply( proof: ResolutionProof ): LKProof = {

    def shouldFlip( p: ResolutionProof ): Boolean = p match {
      case Paramod( _, _, _, q, _, _ ) => shouldFlip( q )
      case Flip( q, _ )                => !shouldFlip( q )
      case Input( _ )                  => false
    }
    def maybeFlip( atom: HOLFormula, flip: Boolean ): HOLFormula =
      if ( flip ) {
        val Eq( t, s ) = atom
        Eq( s, t )
      } else {
        atom
      }

    var lk: LKProof = proof match {
      case Resolution( Refl( term ), _, _, _ ) => ReflexivityAxiom( term )
      case Resolution( left, _, right, _ ) =>
        if ( shouldFlip( right ) ) {
          val Sequent( Seq( Eq( t, s ) ), Seq() ) = right.conclusion
          ResolutionToLKProof.mkSymmProof( t, s )
        } else {
          LogicalAxiom( left.conclusion.succedent.head )
        }
    }

    proof.dagLike.postOrder.reverse.tail.foreach { p =>
      p match {
        case Refl( _ )  =>
        case Input( _ ) =>
        case p @ Paramod( q1, _, _, q2, i2, ctx ) =>
          val shouldFlip2 = shouldFlip( q2 )
          val lkAux = maybeFlip( p.rewrittenAuxFormula, shouldFlip2 )
          if ( lk.conclusion.zipWithIndex.exists { case ( a, i ) => a == lkAux && !i.sameSideAs( i2 ) } ) {
            val lkMain = maybeFlip( p.auxFormula, shouldFlip2 )
            val lkEq = maybeFlip( q1.conclusion( Suc( 0 ) ), shouldFlip( q1 ) )
            lk = WeakeningLeftRule( lk, lkEq )
            if ( i2.isSuc )
              lk = EqualityLeftRule( lk, lkEq, lkAux, lkMain )
            else
              lk = EqualityRightRule( lk, lkEq, lkAux, lkMain )
          }
        case Flip( _, _ ) =>
      }

      lk = ContractionMacroRule( lk )
    }

    val expectedConclusion = proof.subProofs.collect { case Input( seq ) => seq.swapped }.fold( Sequent() )( _ ++ _ )

    require(
      lk.conclusion isSubMultisetOf expectedConclusion,
      s"$expectedConclusion\n$proof\n$lk"
    )

    lk
  }

}
