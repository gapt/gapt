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

enum NotVerifiedReason {
  case UnexpectedInput(message: String)
  case CannotHandleInput(message: String, stepName: String | TptpInput)
  case UnexpectedException(throwable: Throwable)
  case Timeout

  override def toString(): String = this match
    case UnexpectedInput(message)             => message
    case CannotHandleInput(message, stepName) => s"CannotHandleInput: $message (step: $stepName)"
    case UnexpectedException(throwable)       => s"unexpected exception: ${throwable.printStackTrace()}"
    case Timeout                              => "Timeout"
}

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
}
import OtherFailureReason._

type FailedVerifiedReason =
  TptpDerivationImportError | OtherFailureReason

enum SzsStatus {
  case VerifiedGood
  case VerifiedBad(reason: FailedVerifiedReason)
  case Unknown(reason: NotVerifiedReason)

  def status: String = this match {
    case VerifiedGood        => "VerifiedGood"
    case VerifiedBad(reason) => s"VerifiedBad : $reason"
    case Unknown(_)          => "Unknown"
  }
  def isGood: Boolean = this == VerifiedGood
  def isBad: Boolean = this.isInstanceOf[VerifiedBad]
  def isUnknown: Boolean = this.isInstanceOf[Unknown]

  def statusLine: String = s"%SZS status $status"
}

object SzsStatus {
  def failed(reason: FailedVerifiedReason): SzsStatus.VerifiedBad = VerifiedBad(reason)
  def timeout: SzsStatus.Unknown = Unknown(NotVerifiedReason.Timeout)
  def unexpectedInput(message: String): SzsStatus.Unknown = Unknown(NotVerifiedReason.UnexpectedInput(message))
  def cannotHandleInput(message: String, stepName: String | TptpInput): SzsStatus.Unknown = Unknown(NotVerifiedReason.CannotHandleInput(message, stepName))
  def unexpectedException(throwable: Throwable): SzsStatus.Unknown = Unknown(NotVerifiedReason.UnexpectedException(throwable))
  def noConjectureFound(message: String): SzsStatus.Unknown = unexpectedInput(message)
  def noRefutationFound(message: String): SzsStatus.Unknown = unexpectedInput(message)
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
        case _: TimeOutException                  => SzsStatus.timeout
        case t: Throwable                         => SzsStatus.unexpectedException(t)
        case InputSyntaxError(cause)              => SzsStatus.unexpectedInput(s"syntax error: $cause")
        case CannotHandleInput(message, stepName) => SzsStatus.cannotHandleInput(message, stepName)
        case NoConjectureFound(message)           => SzsStatus.noConjectureFound(message)
        case NoRefutationFound(message)           => SzsStatus.noRefutationFound(message)
        case reason: FailedVerifiedReason         => SzsStatus.failed(reason)
      }
    case Right(_) => SzsStatus.VerifiedGood
  }
}

private def checkStepHasCorrectFileDirective(
    s: TptpAxiomStep | TptpConjectureStep,
    fileDirectiveRoot: os.Path
): Either[FailedVerifiedReason, Unit] = boundary {
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
