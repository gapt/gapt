package gapt.formats.tptp.check

import gapt.formats.InputFile
import gapt.formats.tptp.*
import gapt.utils.withTimeout
import gapt.utils.getOrBreak

import scala.concurrent.duration.*
import scala.util.boundary
import boundary.break
import gapt.expr.formula.Formula
import gapt.utils.TimeOutException
import java.nio.file.Paths

enum OtherFailureReason {
  case SourceMissing(stepName: String)
  case FileDirectiveMissing(stepName: String)
  case FileDirectiveLabelMissing(stepName: String)
  case FileDirectiveFileNotFound(stepName: String, absolutePath: os.Path)
  case FileDirectiveInvalidSyntax(stepName: String, absolutePath: os.Path)
  case FileDirectiveFileDoesNotHaveLabel(
      stepName: String,
      absolutePath: os.Path,
      label: String
  )
  case FileDirectiveFileHasMultipleDistinctFormulasWithLabel(
      stepName: String,
      absolutePath: os.Path,
      label: String
  )
  case FileDirectiveStepDoesNotMatchRole(
      stepName: String,
      absolutePath: os.Path,
      label: String,
      expectedRole: String,
      actualRole: String
  )
  case FileDirectiveFormulaNotAlphaEquivalentToClaimedFormula(
      stepName: String,
      absolutePath: os.Path,
      label: String,
      expected: Formula,
      actual: Formula
  )

  def message: String = this match
    case s: SourceMissing =>
      s"step ${s.stepName} is missing a source"
    case s: FileDirectiveMissing =>
      s"step ${s.stepName} is missing a file directive"
    case s: FileDirectiveLabelMissing =>
      s"step ${s.stepName} is missing a file directive label"
    case s: FileDirectiveFileNotFound =>
      s"step ${s.stepName} has a file source (${s.absolutePath}) that could not be found"
    case s: FileDirectiveInvalidSyntax =>
      s"step ${s.stepName} has a file source (${s.absolutePath}) with invalid TPTP syntax"
    case s: FileDirectiveFileDoesNotHaveLabel =>
      s"step ${s.stepName} has a file source (${s.absolutePath}) that does not have the label '${s.label}' referred to in the file directive"
    case s: FileDirectiveFileHasMultipleDistinctFormulasWithLabel =>
      s"step ${s.stepName} has a file source (${s.absolutePath}) that has multiple distinct formulas with the same label '${s.label}'"
    case s: FileDirectiveStepDoesNotMatchRole =>
      s"step ${s.stepName} has a file source (${s.absolutePath}) that points to a formula with name ${s.label} that does not have the same role as the step. expected: ${s.expectedRole}, actual: ${s.actualRole}"
    case s: FileDirectiveFormulaNotAlphaEquivalentToClaimedFormula =>
      s"step ${s.stepName} has a file source (${s.absolutePath}) that points to a formula with name ${s.label} that is not alpha-equivalent to the claimed formula. expected: ${s.expected}, actual: ${s.actual}"

}
import OtherFailureReason._

type VerifiedBadReason =
  IncorrectInference
    | IncorrectSkolemization
    | DeskolemizationFailed
    | InferenceCycle
    | OtherFailureReason
    | StepWithInvalidStatus
    | StepWithMissingParents
    | NegatedConjectureStepWithNonConjectureParent
    | NegatedConjectureWithoutParent
    | PlainInferenceWithConjectureParent
    | NegatedConjectureWithMultipleDistinctParents
    | DistinctFormulasWithSameName
    | ProofReconstructionError

type UnknownReason =
  Throwable
    | InputSyntaxError
    | CannotHandleInput
    | NoConjectureFound
    | NoRefutationFound
    | SkolemizationStepWithNewSymbolDifferingFromSkolemizeTerm
    | SkolemizationStepWithoutBinding
    | SkolemizationStepWithoutNewSymbols
    | UnexpectedInput
    | CannotHandleIncludeDirectives

enum SzsStatus {
  case VerifiedGood
  case VerifiedBad(reason: VerifiedBadReason)
  case Unknown(reason: UnknownReason)
  case Timeout

  def status: String = this match {
    case VerifiedGood                                   => "VerifiedGood"
    case VerifiedBad(reason: TptpDerivationImportError) => s"VerifiedBad : ${reason.message}"
    case VerifiedBad(reason: OtherFailureReason)        => s"VerifiedBad : ${reason.toString}"
    case Unknown(_)                                     => "Unknown"
    case Timeout                                        => "Timeout"
  }
  def isGood: Boolean = this == VerifiedGood
  def isBad: Boolean = this.isInstanceOf[VerifiedBad]
  def isUnknown: Boolean = this.isInstanceOf[Unknown]

  def statusLine: String = s"%SZS status $status"
}

def checkProof(file: InputFile, fileDirectiveRoot: os.Path, timeout: Duration = 25.seconds): SzsStatus = {
  val result = {
    try withTimeout(timeout) {
        boundary {
          val refutation = RootedTptpDerivation.fromInputFileRefutation(file).getOrBreak
          refutation.usedDerivationSteps.foreach {
            case step: (TptpAxiomStep | TptpConjectureStep) =>
              checkStepHasCorrectFileDirective(step, fileDirectiveRoot).getOrBreak
            case _ =>
          }

          val usedNegatedConjectures = refutation.usedDerivationSteps.collect { case s: TptpNegatedConjectureStep => s }
          usedNegatedConjectures.find(s => !s.hasUnambiguousStatusAmong(Set("cth"))).map { s =>
            break(Left(StepWithInvalidStatus(s.name, s.statuses, Set("cth"))))
          }

          val usedPlainInferences = refutation.usedDerivationSteps.collect { case a: TptpPlainInferenceStep => a }
          usedPlainInferences.find(c => !c.hasUnambiguousStatusAmong(Set("thm", "esa"))).map { s =>
            break(Left(StepWithInvalidStatus(s.name, s.statuses, Set("thm", "esa"))))
          }

          val usedSkolemizationSteps = refutation.usedDerivationSteps.collect { case s: TptpSkolemizationStep => s }
          usedSkolemizationSteps.find(s => !s.hasUnambiguousStatusAmong(Set("esa"))).map { s =>
            break(Left(StepWithInvalidStatus(s.name, s.statuses, Set("esa"))))
          }

          TptpImporter.loadAsLKRefutation(file)
        }
      }
    catch e => Left(e)
  }

  result match {
    case Left(reason) => reason match {
        case _: TimeOutException       => SzsStatus.Timeout
        case r: UnknownReason          => SzsStatus.Unknown(r)
        case reason: VerifiedBadReason => SzsStatus.VerifiedBad(reason)
      }
    case Right(_) => SzsStatus.VerifiedGood
  }
}

private def checkStepHasCorrectFileDirective(
    s: TptpAxiomStep | TptpConjectureStep,
    fileDirectiveRoot: os.Path
): Either[VerifiedBadReason, Unit] = boundary {
  val annotations = s.annotationsOption.getOrElse {
    break(Left(SourceMissing(s.name)))
  }
  val (fileName, label) = annotations.source match {
    case Source.File(fileName, Some(label)) => (fileName, label)
    case Source.File(_, None) =>
      break(Left(FileDirectiveLabelMissing(s.name)))
    case _ =>
      break(Left(FileDirectiveMissing(s.name)))
  }

  val absolutePath =
    if Paths.get(fileName).isAbsolute() then os.Path(fileName)
    else fileDirectiveRoot / os.RelPath(fileName)

  if !os.exists(absolutePath) then {
    break(Left(FileDirectiveFileNotFound(s.name, absolutePath)))
  }
  val tptpFile = {
    try TptpImporter.loadWithIncludes(absolutePath, fileDirectiveRoot)
    catch {
      case _: IllegalArgumentException =>
        break(Left(FileDirectiveInvalidSyntax(s.name, absolutePath)))
    }
  }
  val fileDirectiveFormulas = tptpFile.inputs.collect {
    case a: AnnotatedFormula if a.name == label => a
  }
  val fileDirectiveFormula = fileDirectiveFormulas.distinct match {
    case Seq() =>
      break(Left(FileDirectiveFileDoesNotHaveLabel(s.name, absolutePath, label)))
    case Seq(_, _, _*) =>
      break(Left(FileDirectiveFileHasMultipleDistinctFormulasWithLabel(s.name, absolutePath, label)))
    case Seq(a) => a
  }

  if fileDirectiveFormula.role != s.role then {
    break(Left(FileDirectiveStepDoesNotMatchRole(s.name, absolutePath, label, s.role, fileDirectiveFormula.role)))
  }

  if !fileDirectiveFormula.formula.alphaEquals(s.formula) then {
    break(Left(FileDirectiveFormulaNotAlphaEquivalentToClaimedFormula(
      s.name,
      absolutePath,
      label,
      fileDirectiveFormula.formula,
      s.formula
    )))
  }

  Right(())
}

extension (annotations: Option[Annotations]) {
  def hasUnambiguousStatusAmong(statuses: Set[String]): Boolean = boundary {
    val ann = annotations.getOrElse { break(false) }
    val inferenceSource = ann.source.asInferenceOption.getOrElse { break(false) }
    val inferenceStatus = inferenceSource.statuses.singleOption.getOrElse { break(false) }

    statuses.contains(inferenceStatus)
  }
}

extension (step: TptpDerivationStep) {
  def hasUnambiguousStatusAmong(statuses: Set[String]): Boolean = boundary {
    step.annotationsOption.hasUnambiguousStatusAmong(statuses)
  }
}

extension (gt: GeneralTerm) {
  def asStatus: Option[String] = gt match {
    case TptpTerm("status", TptpTerm(value)) => Some(value)
    case _                                   => None
  }
}

extension (usefulInfo: Seq[GeneralTerm]) {
  def statusSet: Set[String] =
    usefulInfo.flatMap(_.asStatus).toSet
}

extension (inference: Source.Inference) {
  def statuses: Set[String] =
    inference.usefulInfo.statusSet
}

extension (step: TptpPlainInferenceStep) {
  def statuses: Set[String] = step.source.statuses
}

extension (step: TptpNegatedConjectureStep) {
  def statuses: Set[String] = step.source.statuses
}

extension (step: TptpSkolemizationStep) {
  def statuses: Set[String] = step.source.statuses
}
