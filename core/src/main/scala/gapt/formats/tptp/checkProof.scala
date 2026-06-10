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
import scala.util.Try

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

extension (source: Source) {
  def asInferenceOption: Option[Source.Inference] = source match {
    case s @ Source.Inference(rule, usefulInfo, parents) => Some(s)
    case _                                               => None
  }
}

extension (annotatedFormula: AnnotatedFormula) {
  def hasUnambiguousStatusAmong(statuses: Set[String]): Boolean = boundary {
    val annotations = annotatedFormula.annotations.getOrElse {
      boundary.break(false)
    }
    val inferenceSource = annotations.source.asInferenceOption.getOrElse {
      boundary.break(false)
    }
    val inferenceStatus = inferenceSource.statuses.singleOption.getOrElse {
      boundary.break(false)
    }

    statuses.contains(inferenceStatus)
  }
}

case class TptpProofMap private (private val map: Map[String, AnnotatedFormula]) extends Map[String, AnnotatedFormula] {
  export map.*
}

object TptpProofMap {
  def apply(steps: Seq[AnnotatedFormula]): Try[TptpProofMap] = Try {
    val map = scala.collection.mutable.Map[String, AnnotatedFormula]()
    for s <- steps do {
      map.updateWith(s.name) {
        case None => Some(s)
        case Some(formula) =>
          throw IllegalArgumentException(
            s"""formula $formula with name ${formula.name} is already present.
               |Attempted to add another formula $s with the same name.""".stripMargin
          )
      }
    }

    new TptpProofMap(map.toMap)
  }
}

// implementation of checkProof that checks the input by constructing a resolution proof from the input
def checkProof1(file: InputFile, timeout: Duration = 25.seconds): SzsStatus = {
  boundary {
    try withTimeout(timeout) {
        val tptpFile = {
          try TptpImporter.loadWithoutIncludes(file)
          catch
            // In this case the input file was not valid TPTP
            case _: IllegalArgumentException => boundary.break(SzsStatus.FailedVerified)
        }

        val annotatedFormulaSteps = tptpFile.inputs.collect {
          case a @ AnnotatedFormula(_, _, _, _, _) => a
        }

        val tptpProofMap = TptpProofMap(annotatedFormulaSteps).getOrElse {
          boundary.break(SzsStatus.FailedVerified)
        }

        val claimedNegatedConjectures = tptpProofMap.values.collect {
          case a @ AnnotatedFormula(_, _, "negated_conjecture", _, _) => a
        }
        if claimedNegatedConjectures.exists(c => !c.hasUnambiguousStatusAmong(Set("cth"))) then {
          boundary.break(SzsStatus.FailedVerified)
        }

        val plainInferences = tptpProofMap.values.collect {
          case a @ AnnotatedFormula(_, _, "plain", _, _) => a
        }
        if plainInferences.exists(c => !c.hasUnambiguousStatusAmong(Set("thm", "esa"))) then {
          boundary.break(SzsStatus.FailedVerified)
        }

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

  if failed.nonEmpty then SzsStatus.FailedVerified
  else if unverified.nonEmpty then SzsStatus.NotVerified
  else SzsStatus.Verified
}
