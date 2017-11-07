package at.logic.gapt.expr.hol

import at.logic.gapt.expr._
import at.logic.gapt.proofs.MutableContext

object skolemize {

  def apply(
    f:              Formula,
    pol:            Polarity = Polarity.InSuccedent,
    proofTheoretic: Boolean  = false )( implicit ctx: MutableContext = MutableContext.guess( f ) ): Formula = {
    def go( f: Formula, pol: Polarity ): Formula =
      f match {
        case Bottom() | Top() | Atom( _, _ ) => f
        case Neg( a )                        => -go( a, !pol )
        case And( a, b )                     => go( a, pol ) & go( b, pol )
        case Or( a, b )                      => go( a, pol ) | go( b, pol )
        case Imp( a, b )                     => go( a, !pol ) --> go( b, pol )
        case Ex( x, a ) if pol.inSuc         => Ex( x, go( a, pol ) )
        case All( x, a ) if pol.inAnt        => All( x, go( a, pol ) )
        case Quant( _, _, _ ) =>
          val fvs = freeVariables( f ).toVector
          val skC = ctx.addSkolemSym( Abs( fvs, f ), reuse = !proofTheoretic )
          go( instantiate( f, skC( fvs ) ), pol )
      }
    go( f, pol )
  }

}
