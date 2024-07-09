package gapt.proofs.ceres2

import gapt.proofs.ceres._
import gapt.cutintro.CutIntroduction
import gapt.examples._
import gapt.expr._
import gapt.expr.formula.fol.Numeral
import gapt.expr.formula.hol.isAtom
import gapt.formats.ClasspathInputFile
import gapt.formats.llk._
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.Sort
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.transformations.cutNormal
import gapt.proofs.{Sequent, SequentMatchers, gaptic}
import gapt.provers.escargot.Escargot
import gapt.utils.SatMatchers
import org.specs2.mutable._

class CeresTest extends Specification with SequentMatchers with SatMatchers {}
