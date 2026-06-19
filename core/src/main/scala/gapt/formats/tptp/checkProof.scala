package gapt.formats.tptp.check

import gapt.formats.InputFile
import gapt.formats.tptp.*
import gapt.formats.tptp.check.NotVerifiedReason.UnexpectedException
import gapt.utils.withTimeout

import scala.concurrent.duration.*

enum NotVerifiedReason {
  case UnexpectedInput(message: String)
  case CannotHandleInput
  case UnexpectedException(throwable: Throwable)
  case Timeout
}

enum SzsStatus {
  case Verified
  case FailedVerified(reason: TptpDerivationImportError)
  case NotVerified(reason: NotVerifiedReason)

  def status: String = this match {
    case Verified               => "Verified"
    case FailedVerified(reason) => s"FailedVerified : $reason"
    case NotVerified(_)         => "NotVerified"
  }
  def statusLine: String = s"%SZS status $status"
}

object SzsStatus {
  def failed(reason: TptpDerivationImportError): SzsStatus.FailedVerified = FailedVerified(reason)
  def timeout: SzsStatus.NotVerified = NotVerified(NotVerifiedReason.Timeout)
  def unexpectedInput(message: String): SzsStatus.NotVerified = NotVerified(NotVerifiedReason.UnexpectedInput(message))
  def cannotHandleInput: SzsStatus.NotVerified = NotVerified(NotVerifiedReason.CannotHandleInput)
  def unexpectedException(throwable: Throwable): SzsStatus.NotVerified = NotVerified(NotVerifiedReason.UnexpectedException(throwable))
  def noConjectureFound(message: String): SzsStatus.NotVerified = unexpectedInput(message)
  def noRefutationFound(message: String): SzsStatus.NotVerified = unexpectedInput(message)
}

def checkProof(file: InputFile, timeout: Duration = 25.seconds): SzsStatus = {
  try
    withTimeout(timeout) {
      TptpImporter.loadAsLKRefutation(file) match {
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
