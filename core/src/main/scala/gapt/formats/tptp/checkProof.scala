package gapt.formats.tptp.check

import gapt.expr.formula.Formula
import gapt.proofs.Sequent
import gapt.expr.formula.Neg
import gapt.utils.withTimeout
import gapt.provers.escargot.Escargot
import gapt.utils.TimeOutException
import gapt.formats.tptp._

enum SzsStatus {
  case Verified
  case FailedVerified
  case NotVerified

  override def toString(): String = this match {
    case Verified       => "Verified"
    case FailedVerified => "FailedVerified"
    case NotVerified    => "NotVerified"
  }

  def statusLine: String = s"%SZS status ${this.toString()}"
}

def checkProof(tptpFile: TptpFile): SzsStatus = {
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
            Seq(TptpTerm("inference", _, _, GeneralList(parents @ _*)))
          ) =>
        // TODO: assert that parent is conjecture?
        Some((input, Sequent(parents.map(p => Neg(getFormulaFromTerm(p))), Seq(formula))))
      case AnnotatedFormula(
            _,
            _,
            _,
            formula,
            Seq(
              TptpTerm(
                "inference",
                TptpTerm("skolemize"),
                TptpTerm(
                  _,
                  TptpTerm("status", TptpTerm("esa")),
                  TptpTerm("new_symbols", TptpTerm("skolem"), GeneralList(new_symbols @ _*)),
                  TptpTerm("skolemized", skolemizedVariable),
                  TptpTerm("bind", bindVariable, bindSymbol)
                ),
                GeneralList(parents @ _*)
              )
            )
          ) => {
        pprint.err.log(new_symbols(0).toRawAsciiString)
        pprint.err.log(skolemizedVariable.toRawAsciiString)
        pprint.err.log((bindVariable.toRawAsciiString, bindSymbol.toAsciiString))
        pprint.err.log(parents)
        ???
      }
      case AnnotatedFormula(
            _,
            _,
            _,
            formula,
            Seq(TptpTerm("inference", _, _, GeneralList(parents @ _*)))
          ) => {
        Some((input, Sequent(parents.map(getFormulaFromTerm), Seq(formula))))
      }
      case _ => None
  }

  pprint.err.log(inferences)

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

  val verified = verifications.filter(_._3.contains(true))
  pprint.err.log(verified)
  val failed = verifications.filter(_._3.contains(false))
  pprint.err.log(failed)
  val unverified = verifications.filter(_._3.isEmpty)
  pprint.err.log(unverified)

  if failed.nonEmpty then SzsStatus.FailedVerified
  else if unverified.nonEmpty then SzsStatus.NotVerified
  else SzsStatus.Verified

  // sketch match {
  //   case Left(error) => {
  //     val errorMessage = error match {
  //       case FileNotFound(f)             => s"file not found: ${f.fileName}"
  //       case ParsingError(file)          => s"parsing error: ${file.fileName}"
  //       case MalformedFile(file)         => s"malformed file: ${file.fileName}"
  //       case StackOverflow(file)         => s"stack overflow when parsing: ${file.fileName}"
  //       case ReconstructionTimeout(file) => s"reconstruction timeout: ${file.fileName}"
  //       case _                           => "unknown error"
  //     }
  //     Console.err.println(errorMessage)
  //     sys.exit(1)
  //     return
  //   }
  //   case Right(_) => {}
  // }

  // val szsStatus = proof match {
  //   case Left(ReconstructionGaveUp(_)
  //       | ReconstructionError(_)) => "FailedVerified"
  //   case Right(_) => "Verified"
  //   case Left(_)  => "NotVerified"
  // }

}
