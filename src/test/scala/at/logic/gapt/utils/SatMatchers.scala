package at.logic.gapt.utils

import at.logic.gapt.expr.{ Neg, FOLFormula }
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.provers.prover9.Prover9Prover
import at.logic.gapt.provers.sat4j.Sat4j
import org.specs2.matcher.OptionMatchers

trait SatMatchers extends OptionMatchers {

  def beUnsat = beNone ^^ { ( f: FOLFormula ) => new Sat4j().solve( f ) }

  val p9 = new Prover9Prover
  def beSat =
    if ( p9 isInstalled )
      beNone ^^ { ( f: FOLFormula ) => p9.getRobinsonProof( f +: Sequent() ) } and
        beSome ^^ { ( f: FOLFormula ) => new Sat4j().solve( f ) }
    else
      beSome ^^ { ( f: FOLFormula ) => new Sat4j().solve( f ) }

  def beValid = beUnsat ^^ { ( f: FOLFormula ) => Neg( f ) }

}
