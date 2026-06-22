package gapt.formats.tptp.check

import gapt.formats.InputFile
import gapt.formats.tptp.*
import gapt.utils.withTimeout
import gapt.utils.getOrBreak

import scala.concurrent.duration.*
import scala.util.boundary
import boundary.break

enum NotVerifiedReason {
  case UnexpectedInput(message: String)
  case CannotHandleInput
  case UnexpectedException(throwable: Throwable)
  case Timeout
}

enum OtherFailureReason {
  case AxiomSourceMissing(stepName: String)
  case AxiomFileDirectiveMissing(stepName: String)
  case AxiomFileDirectiveLabelMissing(stepName: String)
  case AxiomFileDirectiveFileNotFound(stepName: String, fileName: String)
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
  def cannotHandleInput: SzsStatus.NotVerified = NotVerified(NotVerifiedReason.CannotHandleInput)
  def unexpectedException(throwable: Throwable): SzsStatus.NotVerified = NotVerified(NotVerifiedReason.UnexpectedException(throwable))
  def noConjectureFound(message: String): SzsStatus.NotVerified = unexpectedInput(message)
  def noRefutationFound(message: String): SzsStatus.NotVerified = unexpectedInput(message)
}

case class Cwd(path: os.Path)

def checkProof(file: InputFile, timeout: Duration = 25.seconds)(using cwd: Cwd): SzsStatus = {
  try
    withTimeout(timeout) {
      val result = boundary {
        val refutation = RootedTptpDerivation.fromInputFileRefutation(file).getOrBreak
        val usedAxioms = refutation.usedDerivationSteps.collect { case step: TptpAxiomStep => step }
        usedAxioms.map { s =>
          s.annotationsOption match {
            case None => break(Left(AxiomSourceMissing(s.name)))
            case Some(a) => a.source match {
                case Source.File(_, None) =>
                  break(Left(AxiomFileDirectiveLabelMissing(s.name)))
                case Source.File(fileName, Some(label)) => {
                  if !os.exists(cwd.path / os.RelPath(fileName)) then {
                    break(Left(AxiomFileDirectiveFileNotFound(s.name, fileName)))
                  }
                  (s, a)
                }
                case _ =>
                  break(Left(AxiomFileDirectiveMissing(s.name)))
              }
          }
        }

        TptpImporter.loadAsLKRefutation(file)
      }

      result match {
        case Left(reason) => reason match {
            case CannotHandleInput(_, _)    => SzsStatus.cannotHandleInput
            case NoConjectureFound(message) => SzsStatus.noConjectureFound(message)
            case NoRefutationFound(message) => SzsStatus.noRefutationFound(message)
            case _                          => SzsStatus.failed(reason)
          }
        case Right(_) => SzsStatus.Verified
      }
    }
  catch e => SzsStatus.unexpectedException(e)
}
