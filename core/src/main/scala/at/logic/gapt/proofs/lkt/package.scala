package at.logic.gapt.proofs

package object lkt extends ImplicitInstances {

  implicit class HypSet( private val set: Set[Hyp] ) extends AnyVal {
    private def freshIdx: Int =
      if ( set.isEmpty ) 1 else set.view.map( h => math.abs( h.idx ) ).max + 1
    def freshSuc: Hyp = Hyp( freshIdx )
    def freshAnt: Hyp = Hyp( -freshIdx )
    def freshSameSide( h: Hyp ): Hyp = if ( h.inAnt ) freshAnt else freshSuc
  }

}
