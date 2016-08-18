package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr.{ Eq, HOLFormula }
import at.logic.gapt.proofs.{ Ant, Suc }
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
        val sucEq = maybeFlip( right.conclusion( Ant( 0 ) ), shouldFlip( right ) )
        val antEq = maybeFlip( left.conclusion( Suc( 0 ) ), shouldFlip( left ) )
        ( antEq, sucEq ) match {
          case ( x, y ) if x == y => LogicalAxiom( x )
          case ( Eq( t, s ), Eq( s_, t_ ) ) if t == t_ && s == s_ =>
            ResolutionToLKProof.mkSymmProof( t, s )
        }
    }

    proof.dagLike.postOrder.reverse.tail.foreach { p =>
      p match {
        case Refl( _ )  =>
        case Input( _ ) =>
        case p @ Paramod( q1, _, _, q2, i2, ctx ) =>
          val shouldFlip2 = shouldFlip( q2 )
          val lkAux = maybeFlip( p.rewrittenAuxFormula, shouldFlip2 )
          if ( lk.conclusion.contains( lkAux, !i2.polarity ) ) {
            val lkMain = maybeFlip( p.auxFormula, shouldFlip2 )
            val lkEq = maybeFlip( q1.conclusion( Suc( 0 ) ), shouldFlip( q1 ) )
            if ( ( i2.isSuc && lkEq == lkAux ) || !lk.conclusion.antecedent.contains( lkEq ) ) {
              lk = WeakeningLeftRule( lk, lkEq )
            }
            if ( i2.isSuc )
              lk = EqualityLeftRule( lk, lkEq, lkAux, lkMain )
            else
              lk = EqualityRightRule( lk, lkEq, lkAux, lkMain )
          }
        case Flip( _, _ ) =>
      }

      if ( lk.conclusion.isTaut ) {
        lk = LogicalAxiom( lk.conclusion.antecedent intersect lk.conclusion.succedent head )
      } else {
        lk = ContractionMacroRule( lk )
      }
    }

    val expectedConclusion = proof.subProofs.collect { case Input( seq ) => seq.swapped }.flattenS

    require(
      lk.conclusion isSubMultisetOf expectedConclusion,
      s"$expectedConclusion\n$proof\n$lk"
    )

    lk
  }

}
