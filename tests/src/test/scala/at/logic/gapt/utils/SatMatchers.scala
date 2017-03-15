package at.logic.gapt.utils

import at.logic.gapt.expr.Formula
import at.logic.gapt.proofs.{ HOLSequent, Sequent }
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.groundFreeVariables
import at.logic.gapt.provers.sat.Sat4j
import org.specs2.matcher.OptionMatchers

trait SatMatchers extends OptionMatchers {

  def beUnsat = beNone ^^ { ( f: Formula ) => Sat4j.solve( f ) }

  def beSat =
    beNone ^^ { ( f: Formula ) => new Escargot( splitting = false, equality = false, propositional = true ).getResolutionProof( f ) } and
      beSome ^^ { ( f: Formula ) => Sat4j.solve( f ) }
  def beValid = beUnsat ^^ { ( f: Formula ) => -f }
  def beValidSequent = beValid ^^ { ( sequent: HOLSequent ) => sequent.toDisjunction }

  def beEUnsat =
    beSome ^^ { ( f: Formula ) => new Escargot( splitting = false, equality = true, propositional = true ).getResolutionProof( -f ) }
  def beEValid = beEUnsat ^^ { ( f: Formula ) => -f }
  def beEValidSequent = beEValid ^^ { ( sequent: HOLSequent ) => sequent.toDisjunction }

}
