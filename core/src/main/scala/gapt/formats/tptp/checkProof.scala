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
  case AxiomSourceMissing(stepName: String)
  case AxiomFileDirectiveMissing(stepName: String)
  case AxiomFileDirectiveLabelMissing(stepName: String)
  case AxiomFileDirectiveFileNotFound(stepName: String, absolutePath: os.Path)
  case AxiomFileDirectiveInvalidSyntax(stepName: String, absolutePath: os.Path)
  case AxiomFileDirectiveFileDoesNotHaveLabel(stepName: String, absolutePath: os.Path, label: String)
  case AxiomFileDirectiveFormulaHasMultipleDistinctFormulasWithLabel(
      stepName: String,
      absolutePath: os.Path,
      label: String
  )
  case AxiomFileDirectiveStepIsNotAnAxiom(stepName: String, absolutePath: os.Path, label: String)
  case AxiomFileDirectiveFormulaNotAlphaEquivalentToClaimedFormula(
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
  case Verified
  case FailedVerified(reason: FailedVerifiedReason)
  case NotVerified(reason: NotVerifiedReason)

  def status: String = this match {
    case Verified               => "Verified"
    case FailedVerified(reason) => s"FailedVerified : $reason"
    case NotVerified(_)         => "NotVerified"
  }
  def statusLine: String = s"%SZS status $status"
}

object SzsStatus {
  def failed(reason: FailedVerifiedReason): SzsStatus.FailedVerified = FailedVerified(reason)
  def timeout: SzsStatus.NotVerified = NotVerified(NotVerifiedReason.Timeout)
  def unexpectedInput(message: String): SzsStatus.NotVerified = NotVerified(NotVerifiedReason.UnexpectedInput(message))
  def cannotHandleInput(message: String, stepName: String | TptpInput): SzsStatus.NotVerified = NotVerified(NotVerifiedReason.CannotHandleInput(message, stepName))
  def unexpectedException(throwable: Throwable): SzsStatus.NotVerified = NotVerified(NotVerifiedReason.UnexpectedException(throwable))
  def noConjectureFound(message: String): SzsStatus.NotVerified = unexpectedInput(message)
  def noRefutationFound(message: String): SzsStatus.NotVerified = unexpectedInput(message)
}

def checkProof(file: InputFile, fileDirectiveRoot: os.Path, timeout: Duration = 25.seconds): SzsStatus = {
  val result = {
    try withTimeout(timeout) {
        boundary {
          val refutation = RootedTptpDerivation.fromInputFileRefutation(file).getOrBreak
          val usedAxioms = refutation.usedDerivationSteps.collect { case step: TptpAxiomStep => step }
          usedAxioms.foreach { s => checkAxiomStep(s, fileDirectiveRoot).getOrBreak }

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
    case Right(_) => SzsStatus.Verified
  }
}

private def checkAxiomStep(s: TptpAxiomStep, fileDirectiveRoot: os.Path): Either[FailedVerifiedReason, Unit] = boundary {
  val annotations = s.annotationsOption.getOrElse {
    break(Left(AxiomSourceMissing(s.name)))
  }
  val (fileName, label) = annotations.source match {
    case Source.File(fileName, Some(label)) => (fileName, label)
    case Source.File(_, None) =>
      break(Left(AxiomFileDirectiveLabelMissing(s.name)))
    case _ =>
      break(Left(AxiomFileDirectiveMissing(s.name)))
  }

  val absolutePath =
    if Paths.get(fileName).isAbsolute() then os.Path(fileName)
    else fileDirectiveRoot / os.RelPath(fileName)

  if !os.exists(absolutePath) then {
    break(Left(AxiomFileDirectiveFileNotFound(s.name, absolutePath)))
  }
  val tptpFile = {
    try TptpImporter.loadWithIncludes(absolutePath, fileDirectiveRoot)
    catch {
      case _: IllegalArgumentException =>
        break(Left(AxiomFileDirectiveInvalidSyntax(s.name, absolutePath)))
    }
  }
  val fileDirectiveFormulas = tptpFile.inputs.collect {
    case a: AnnotatedFormula if a.name == label => a
  }
  val fileDirectiveFormula = fileDirectiveFormulas.distinct match {
    case Seq() =>
      break(Left(AxiomFileDirectiveFileDoesNotHaveLabel(s.name, absolutePath, label)))
    case Seq(_, _, _*) =>
      break(Left(AxiomFileDirectiveFormulaHasMultipleDistinctFormulasWithLabel(s.name, absolutePath, label)))
    case Seq(a) => a
  }

  if fileDirectiveFormula.role != "axiom" then {
    break(Left(AxiomFileDirectiveStepIsNotAnAxiom(s.name, absolutePath, label)))
  }

  if !fileDirectiveFormula.formula.alphaEquals(s.formula) then {
    break(Left(AxiomFileDirectiveFormulaNotAlphaEquivalentToClaimedFormula(s.name, absolutePath, label, fileDirectiveFormula.formula, s.formula)))
  }

  Right(())
}
