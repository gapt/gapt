package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr.Polarity.{ Negative, Positive }
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable.Specification

class deskolemizeETTest extends Specification with SatMatchers {

  "DrinkersParadox deskolemization" in {

    val x0 = Var( "x_0", Ti )
    val s0 = Const( "s_0", Ti -> Ti )
    val s0x0 = App( s0, x0 )
    val seq = Sequent() :+ ETWeakQuantifier( hof"?x (P x -> !y (x = x & P y))", collection.immutable.ListMap(
      x0 -> ETImp(
        ETWeakening( hof"P ${x0.name}", Negative ),
        ETSkolemQuantifier( hof"!y (${x0.name} = ${x0.name} & P y)", s0x0, Abs( Var( "x", Ti ), hof"!y (x = x & P y)" ),
          ETAnd( ETAtom( hoa"${x0.name} = ${x0.name}", Positive ), ETAtom( hoa"P (${s0.name} ${x0.name})", Positive ) ) )
      ),
      s0x0 -> ETImp(
        ETAtom( hoa"P (${s0.name} ${x0.name})", Negative ),
        ETWeakening( hof"!y ((${s0.name} ${x0.name}) = (${s0.name} ${x0.name}) & P y)", Positive )
      )
    ) )

    /* TODO: Matching with desk does not work for some reason
    val v0 = Var( "v", Ti )
    val desk = Sequent() :+ ETWeakQuantifier( hof"?x (P x -> !y (x = x & P y))", collection.immutable.ListMap(
      x0 -> ETImp(
        ETWeakening( hof"P ${x0.name}", Negative ),
        ETStrongQuantifier( hof"!y (${x0.name} = ${x0.name} & P y)", v0,
          ETAnd( ETAtom( hoa"${x0.name} = ${x0.name}", Positive ), ETAtom( hoa"P ${v0.name}", Positive ) ) )
      ),
      v0 -> ETImp(
        ETAtom( hoa"P ${v0.name}", Negative ),
        ETWeakening( hof"!y (${v0.name} = ${v0.name} & P y)", Positive )
      )
    ) )
    */

    Escargot.isValid( ExpansionProof( seq ).deep ) mustEqual true
    Escargot.isValid( deskolemizeET( ExpansionProof( seq ) ).deep ) mustEqual true
  }

}
