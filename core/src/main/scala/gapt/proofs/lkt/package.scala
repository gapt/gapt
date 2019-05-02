package gapt.proofs

import gapt.logic.Polarity

package object lkt extends ImplicitInstances {

  implicit class HypSet( private val set: Set[Hyp] ) extends AnyVal {
    private def freshIdx: Int =
      if ( set.isEmpty ) 1 else set.view.map( h => math.abs( h.idx ) ).max + 1
    def freshSuc: Hyp = Hyp( freshIdx )
    def freshAnt: Hyp = Hyp( -freshIdx )
    def fresh( p: Polarity ): Hyp = if ( p.inAnt ) freshAnt else freshSuc
    def freshSameSide( h: Hyp ): Hyp = if ( h.inAnt ) freshAnt else freshSuc
    def freshSameSide( hs: List[Hyp] ): List[Hyp] =
      ( freshIdx until Int.MaxValue, hs ).zipped.map( ( i, h ) => if ( h.inAnt ) Hyp( -i ) else Hyp( i ) ).toList
  }

}
