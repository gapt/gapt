package gapt.formats.tptp

import gapt.logic.hol.CNFp
import gapt.proofs.Sequent
import gapt.proofs.resolution.{Input, ResolutionProof}

object TptpProblemToResolution {
  def apply(tptpFile: TptpFile): Set[ResolutionProof] =
    tptpFile.inputs.map {
      case AnnotatedFormula("cnf", _, _, formula, _) =>
        CNFp(formula).toSeq match {
          case Seq(clause) => Input(clause)
          case _           =>
            // e.g. tautologies
            Input(Sequent() :+ formula)
        }
      case AnnotatedFormula(_, _, "conjecture", formula, _) =>
        Input(formula +: Sequent())
      case AnnotatedFormula(_, _, _, formula, _) =>
        Input(Sequent() :+ formula)
      case input => throw new IllegalArgumentException(input.toString)
    }.toSet

}
