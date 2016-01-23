package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.{ parseFormula, parseTerm }

object lattice {
  private val Seq( x, x_0, y, y_0, z, z_0, s, t ) = Seq( "x", "x_0", "y", "y_0", "z", "z_0", "s", "t" ) map {
    FOLVar( _ )
  }

  private val cap = FOLFunctionConst( "\\cap", 2 )
  private val cup = FOLFunctionConst( "\\cup", 2 )

  private val L1 = All( x, All( y, Imp( Eq( cap( x, y ), x ), Eq( cup( x, y ), y ) ) ) )
  private val L2 = And( All( x, All( y, cup( cap( x, y ), Eq( x, x ) ) ) ), All( x, All( y, cap( cup( x, y ), Eq( x, x ) ) ) ) )
  private val L3 = ???

  val p1_3 = ???
  val p3_2 = ???

  val p = Lemma( Sequent( Seq( "L1" -> L1 ), Seq( "L2" -> L2 ) ) ) {
    cut( L3, "L3" )
    insert( p1_3 )
    insert( p3_2 )
  }
}
