package at.logic.gapt.utils

import at.logic.gapt.expr.Formula
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.renameConstantsToFi
import at.logic.gapt.provers.sat.Sat4j
import org.specs2.matcher.OptionMatchers

trait SatMatchers extends OptionMatchers {

  def beUnsat = beNone ^^ { ( f: Formula ) => Sat4j.solve( f ) }

  def beSat =
    beNone ^^ { ( f: Formula ) =>
      renameConstantsToFi.wrap( f )( ( _, mangled: Formula ) =>
        new Escargot( splitting = false, equality = false, propositional = true )
          .getResolutionProof( mangled ) )
    } and
      beSome ^^ { ( f: Formula ) => Sat4j.solve( f ) }
  def beValid = beUnsat ^^ { ( f: Formula ) => -f }
  def beValidSequent = beValid ^^ { ( sequent: HOLSequent ) => sequent.toDisjunction }

  def beEUnsat =
    beSome ^^ { ( f: Formula ) =>
      renameConstantsToFi.wrap( -f )( ( _, mangled: Formula ) =>
        new Escargot( splitting = false, equality = true, propositional = true )
          .getResolutionProof( mangled ) )
    }
  def beEValid = beEUnsat ^^ { ( f: Formula ) => -f }
  def beEValidSequent = beEValid ^^ { ( sequent: HOLSequent ) => sequent.toDisjunction }

}
