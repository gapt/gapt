package gapt.utils

import gapt.expr.Formula
import gapt.proofs.HOLSequent
import gapt.provers.escargot.Escargot
import gapt.provers.renameConstantsToFi
import gapt.provers.sat.Sat4j
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

  def beEValid =
    beSome ^^ { ( f: Formula ) =>
      renameConstantsToFi.wrap( f )( ( _, mangled: Formula ) =>
        new Escargot( splitting = false, equality = true, propositional = true )
          .getResolutionProof( mangled ) )
    }
  def beEUnsat = beEValid ^^ { ( f: Formula ) => -f }
  def beEValidSequent = beEValid ^^ { ( sequent: HOLSequent ) => sequent.toDisjunction }

}
