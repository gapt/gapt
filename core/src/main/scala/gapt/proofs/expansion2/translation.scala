package gapt.proofs.expansion2
import gapt.proofs.{ expansion => old }

object ETtoET2 {
  def apply( et: old.ExpansionTree ): ExpansionTree = ExpansionTree( et.shallow, et.polarity, ETtoETt2( et ) )
  def apply( es: old.ExpansionSequent ): ExpansionSequent = es.map( apply )
  def apply( ep: old.ExpansionProof ): ExpansionProof = ExpansionProof( apply( ep.expansionSequent ) )
}

object ETtoETt2 {
  def apply( et: old.ExpansionTree ): ETt = et match {
    case old.ETAtom( _, _ )                 => ETtAtom
    case old.ETMerge( a, b )                => ETtMerge( apply( a ), apply( b ) )
    case old.ETWeakening( _, _ )            => ETtWeakening
    case old.ETTop( _ ) | old.ETBottom( _ ) => ETtNullary
    case old.ETNeg( ch )                    => ETtUnary( apply( ch ) )
    case old.ETAnd( ch1, ch2 )              => ETtBinary( apply( ch1 ), apply( ch2 ) )
    case old.ETOr( ch1, ch2 )               => ETtBinary( apply( ch1 ), apply( ch2 ) )
    case old.ETImp( ch1, ch2 )              => ETtBinary( apply( ch1 ), apply( ch2 ) )
    case old.ETWeakQuantifier( _, insts ) =>
      ETtWeak( for ( ( inst, ch ) <- insts ) yield inst -> apply( ch ) )
    case old.ETStrongQuantifier( _, ev, ch ) =>
      ETtStrong( ev, apply( ch ) )
    case old.ETSkolemQuantifier( _, skT, skD, ch ) =>
      ETtSkolem( skT, skD, apply( ch ) )
    case old.ETDefinition( _, ch ) =>
      ETtDef( ch.shallow, apply( ch ) )
  }
}
