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

def checkProof(file: InputFile): SzsStatus = checkProof1(file)

// implementation of checkProof that checks the input by constructing a resolution proof from the input
def checkProof1(file: InputFile, timeout: Duration = 25.seconds): SzsStatus = {
  import scala.util.boundary
  boundary {
    try withTimeout(timeout) {
        val tptpRefutationSketch = TptpProofParser.parseTptpRefutationSketch(file)
        tptpRefutationSketch.conjectureNegatedConjecturePair match {
          case Some((conjecture, negatedConjecture)) =>
            if !Escargot.isValid(Neg(conjecture) --> negatedConjecture) then
              boundary.break(SzsStatus.FailedVerified)
          case None =>
        }

        val sketch = tptpRefutationSketch.refutationSketch
        val proof = RefutationSketchToResolution(sketch)
        proof match {
          case Left(UnprovableSketchInference(_)) => SzsStatus.FailedVerified
          case Right(_)                           => SzsStatus.Verified
        }
      }
    catch {
      case _: TimeOutException => {
        SzsStatus.NotVerified
      }
    }
  }
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
  val failed = verifications.filter(_._3.contains(false))
  val unverified = verifications.filter(_._3.isEmpty)

  if failed.nonEmpty then SzsStatus.FailedVerified
  else if unverified.nonEmpty then SzsStatus.NotVerified
  else SzsStatus.Verified
}
