package at.logic.gapt.utils

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.sat.Sat4j
import org.specs2.matcher.OptionMatchers

trait SatMatchers extends OptionMatchers {

  def beUnsat = beNone ^^ { ( f: HOLFormula ) => Sat4j.solve( f ) }

  val p9 = Prover9
  def beSat =
    if ( p9 isInstalled )
      beNone ^^ { ( f: HOLFormula ) => p9.getRobinsonProof( f +: Sequent() ) } and
        beSome ^^ { ( f: HOLFormula ) => Sat4j.solve( f ) }
    else
      beSome ^^ { ( f: HOLFormula ) => Sat4j.solve( f ) }

  def beValid = beUnsat ^^ { ( f: HOLFormula ) => -f }

}
