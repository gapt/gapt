package gapt.utils

import gapt.expr.formula.Formula
import gapt.proofs.HOLSequent
import gapt.proofs.expansion.ExpansionProof
import gapt.provers.escargot.Escargot
import gapt.provers.renameConstantsToFi
import gapt.provers.sat.Sat4j
import org.specs2.matcher.OptionMatchers
import gapt.proofs.resolution.ResolutionProof
import gapt.proofs.resolution.resolutionProofsAreReplaceable
import gapt.proofs.RichFormulaSequent
import gapt.models.PropositionalModel

trait SatMatchers extends OptionMatchers {

  def beUnsat = beNone ^^ { ( f: Formula ) => Sat4j.solve( f ) }

  def beSat =
    beNone ^^ { ( f: Formula ) =>
      renameConstantsToFi.wrap( f )( ( _, mangled: Formula ) =>
        new Escargot( splitting = false, equality = false, propositional = true )
          .getResolutionProof( mangled ) )
    } and
      (beSome[PropositionalModel]) ^^ { ( f: Formula ) => Sat4j.solve( f ) }
  def beValid = beUnsat ^^ { ( f: Formula ) => -f }
  def beValidSequent = beValid ^^ { ( sequent: HOLSequent ) => sequent.toDisjunction }

  def beEValid =
    (beSome[ResolutionProof]) ^^ { ( f: Formula ) =>
      renameConstantsToFi.wrap( f )( ( _, mangled: Formula ) =>
        new Escargot( splitting = false, equality = true, propositional = true )
          .getResolutionProof( mangled ) )
    }
  def beEUnsat = beEValid ^^ { ( f: Formula ) => -f }
  def beEValidSequent = beEValid ^^ { ( sequent: HOLSequent ) => sequent.toDisjunction }

  def havingTautDeepSequent = beValidSequent ^^ { ( ep: ExpansionProof ) => ep.deep }
  def havingQTautDeepSequent = beEValidSequent ^^ { ( ep: ExpansionProof ) => ep.deep }

}
