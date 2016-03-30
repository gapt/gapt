package at.logic.gapt.proofs.epsilon

import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.expr._
import at.logic.gapt.proofs.HOLSequent

case class CriticalFormula( existential: HOLFormula, term: LambdaExpression ) {
  val Ex( bound, qfFormula ) = existential
  val eps = Epsilon( bound, qfFormula )

  val formula = instantiate( existential, term ) --> instantiate( existential, eps )
}

case class EpsilonProof(
    criticalFormula: Seq[CriticalFormula],
    shallow:         HOLSequent
) {
  val deep = criticalFormula.map( _.formula ) ++: shallow.map( epsilonize( _ ) )

  override def toString = deep.toString
}

object epsilonize {
  def apply( f: HOLFormula ): HOLFormula = f match {
    case Top() | Bottom() | HOLAtom( _, _ ) => f
    case Neg( a )                           => Neg( apply( a ) )
    case And( a, b )                        => And( apply( a ), apply( b ) )
    case Or( a, b )                         => Or( apply( a ), apply( b ) )
    case Imp( a, b )                        => Imp( apply( a ), apply( b ) )
    case Ex( x, a ) =>
      val a_ = apply( a )
      Substitution( x -> Epsilon( x, a_ ) )( a_ )
    case All( x, a ) =>
      val a_ = apply( a )
      Substitution( x -> Epsilon( x, -a_ ) )( a_ )
  }
}