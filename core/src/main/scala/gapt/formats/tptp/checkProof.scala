package gapt.formats.tptp.check

import gapt.formats.InputFile
import gapt.formats.tptp.*
import gapt.proofs.sketch.RefutationSketchToResolution
import gapt.expr.formula.Formula
import gapt.proofs.Sequent
import gapt.expr.formula.Neg
import gapt.utils.withTimeout
import gapt.provers.escargot.Escargot
import gapt.utils.TimeOutException
import gapt.proofs.sketch.UnprovableSketchInference
import scala.concurrent.duration._
import gapt.expr.Expr
import scala.util.boundary
import boundary.break
import gapt.formats.tptp.check.NotVerifiedReason.UnexpectedException

enum NotVerifiedReason {
  case UnexpectedInput
  case CannotHandleInput
  case UnexpectedException(throwable: Throwable)
  case Timeout
}

enum SzsStatus {
  case Verified
  case FailedVerified(reason: TptpProofImportError)
  case NotVerified(reason: NotVerifiedReason)

  def status: String = this match {
    case Verified               => "Verified"
    case FailedVerified(reason) => s"FailedVerified : $reason"
    case NotVerified(_)         => "NotVerified"
  }
  def statusLine: String = s"%SZS status $status"
}

object SzsStatus {
  def failed(reason: TptpProofImportError): SzsStatus.FailedVerified = FailedVerified(reason)
  def timeout: SzsStatus.NotVerified = NotVerified(NotVerifiedReason.Timeout)
  def unexpectedInput: SzsStatus.NotVerified = NotVerified(NotVerifiedReason.UnexpectedInput)
  def cannotHandleInput: SzsStatus.NotVerified = NotVerified(NotVerifiedReason.CannotHandleInput)
  def unexpectedException(throwable: Throwable): SzsStatus.NotVerified = NotVerified(NotVerifiedReason.UnexpectedException(throwable))
}

def checkProof(file: InputFile): SzsStatus = checkProof1(file)

// implementation of checkProof that checks the input by constructing a resolution proof from the input
def checkProof1(file: InputFile, timeout: Duration = 25.seconds): SzsStatus = {
  try boundary {
      withTimeout(timeout) {
        val tptpRefutationSketch = TptpProofParser.parseTptpRefutationSketch(file) match {
          case Left(TptpProofImportError.CannotHandleInput(input)) =>
            break(SzsStatus.cannotHandleInput)
          case Left(reason)  => break(SzsStatus.failed(reason))
          case Right(sketch) => sketch
        }
        tptpRefutationSketch.conjectureNegatedConjecturePair match {
          case Some((conjecture, negatedConjecture)) =>
            if !Escargot.isValid(Neg(conjecture) --> negatedConjecture) then
              break(SzsStatus.failed(TptpProofImportError.IncorrectNegatedConjectureInference))
          case None =>
        }

        val sketch = tptpRefutationSketch.refutationSketch
        val proof = RefutationSketchToResolution(sketch)
        proof match {
          case Left(UnprovableSketchInference(_)) => SzsStatus.failed(TptpProofImportError.IncorrectPlainInference)
          case Right(_)                           => SzsStatus.Verified
        }
      }
    }
  catch e => SzsStatus.unexpectedException(e)
}

// implementation of checkProof that only performs the proof checking without constructing the proof
def checkProof2(file: InputFile): SzsStatus = {
  val tptpFile = TptpImporter.loadWithoutIncludes(file)
  if !tptpFile.inputs.exists {
      case AnnotatedFormula(_, _, "conjecture", _, _) => true
      case _                                          => false
    }
  then throw IllegalArgumentException("No conjecture found")

  val formulaLabels = tptpFile.inputs.foldLeft(Map.empty[String, Formula]) { (acc, input) =>
    input match
      case AnnotatedFormula(_, name, _, formula, _) => acc + (name -> formula)
      case IncludeDirective(_, _)                   => acc
  }

  def getFormulaFromTerm(term: GeneralTerm): Formula = term match {
    case TptpTerm(name) => formulaLabels(name)
  }

  val inferences: Seq[(TptpInput, Sequent[Formula])] = tptpFile.inputs.flatMap { input =>
    input match
      case AnnotatedFormula(
            _,
            _,
            "negated_conjecture",
            formula,
            Some(Annotations(Source.Inference(_, _, GeneralList(parents @ _*)), _))
          ) =>
        // TODO: assert that parent is conjecture?
        Some((input, Sequent(parents.map(p => Neg(getFormulaFromTerm(p))), Seq(formula))))
      case AnnotatedFormula(
            _,
            _,
            _,
            formula,
            Some(Annotations(
              Source.Inference(
                "skolemize",
                TptpTerm(
                  _,
                  TptpTerm("status", TptpTerm("esa")),
                  TptpTerm("new_symbols", TptpTerm("skolem"), GeneralList(new_symbols @ _*)),
                  TptpTerm("skolemized", skolemizedVariable),
                  TptpTerm("bind", bindVariable, bindSymbol)
                ),
                GeneralList(parents @ _*)
              ),
              _
            ))
          ) => {
        ???
      }
      case AnnotatedFormula(
            _,
            _,
            _,
            formula,
            Some(Annotations(Source.Inference(_, _, GeneralList(parents @ _*)), _))
          ) => {
        Some((input, Sequent(parents.map(getFormulaFromTerm), Seq(formula))))
      }
      case _ => None
  }

  import scala.concurrent.duration._
  val verifications = inferences.map {
    case (input, sequent) =>
      val verification =
        try {
          withTimeout(10.seconds) {
            Some(Escargot.isValid(sequent))
          }
        } catch {
          case _: TimeOutException => None
        }
      (input, sequent, verification)
  }

  // val  = verifications.filter(_._3.contains(true))
  val failed = verifications.filter(_._3.contains(false))
  val unverified = verifications.filter(_._3.isEmpty)

  if failed.nonEmpty then SzsStatus.failed(TptpProofImportError.IncorrectPlainInference)
  else if unverified.nonEmpty then SzsStatus.timeout
  else SzsStatus.Verified
}
