package at.logic.gapt.proofs.epsilon

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.proofs.expansion._

object ExpansionProofToEpsilon {

  def apply( e: ExpansionProof ): EpsilonProof = {
    val skolemToEpsilonMap = e.skolemFunctions.skolemDefs.map {
      case ( sk, Abs.Block( vs, q @ Quant( x, _, isForall ) ) ) =>
        val x_ = rename( x, vs )
        ( sk: Expr ) -> Abs.Block( vs, Epsilon( x_, epsilonize(
          if ( isForall ) -instantiate( q, x_ ) else instantiate( q, x_ )
        ) ) )
    }
    def replaceSkolemByEpsilon( t: Expr ) =
      BetaReduction.betaNormalize( TermReplacement( t, skolemToEpsilonMap ) )

    val criticalFormulas = e.subProofs flatMap {
      case ETWeakQuantifier( sh, insts ) =>
        val ex = sh match {
          case All( x, f ) => Ex( x, -epsilonize( replaceSkolemByEpsilon( f ).asInstanceOf[Formula] ) )
          case Ex( x, f )  => Ex( x, epsilonize( replaceSkolemByEpsilon( f ).asInstanceOf[Formula] ) )
        }
        for ( ( term, _ ) <- insts ) yield CriticalFormula( ex, replaceSkolemByEpsilon( term ) )
      case ETStrongQuantifier( _, _, _ ) =>
        throw new IllegalArgumentException
      case _ => Set()
    }

    EpsilonProof( criticalFormulas.toSeq, e.shallow )
  }

}
