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
import gapt.utils.Logger

enum OtherFailureReason {
  case SourceMissing(stepName: String)
  case FileDirectiveMissing(stepName: String)
  case FileDirectiveLabelMissing(stepName: String)
  case FileDirectiveFileNotFound(stepName: String, fileName: String)
  case FileDirectiveInvalidSyntax(stepName: String, fileName: String)
  case FileDirectiveFileDoesNotHaveLabel(
      stepName: String,
      fileName: String,
      label: String
  )
  case FileDirectiveFileHasMultipleFormulasWithSameLabel(
      stepName: String,
      fileName: String,
      label: String
  )
  case FileDirectiveStepDoesNotMatchRole(
      stepName: String,
      fileName: String,
      label: String,
      expectedRole: String,
      actualRole: String
  )
  case FileDirectiveFormulaNotAlphaEquivalentToClaimedFormula(
      stepName: String,
      fileName: String,
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
      s"step ${s.stepName} has a file source (${s.fileName}) that could not be found"
    case s: FileDirectiveInvalidSyntax =>
      s"step ${s.stepName} has a file source (${s.fileName}) with invalid TPTP syntax"
    case s: FileDirectiveFileDoesNotHaveLabel =>
      s"step ${s.stepName} has a file source (${s.fileName}) that does not have the label '${s.label}' referred to in the file directive"
    case s: FileDirectiveFileHasMultipleFormulasWithSameLabel =>
      s"step ${s.stepName} has a file source (${s.fileName}) that has multiple distinct formulas with the same label '${s.label}'"
    case s: FileDirectiveStepDoesNotMatchRole =>
      s"step ${s.stepName} has a file source (${s.fileName}) that points to a formula with name ${s.label} that does not have the same role as the step. expected: ${s.expectedRole}, actual: ${s.actualRole}"
    case s: FileDirectiveFormulaNotAlphaEquivalentToClaimedFormula =>
      s"step ${s.stepName} has a file source (${s.fileName}) that points to a formula with name ${s.label} that is not alpha-equivalent to the claimed formula. expected: ${s.expected}, actual: ${s.actual}"

}
import OtherFailureReason._

type VerifiedBadReason =
  IncorrectInference
    | IncorrectSkolemization
    | SkolemizationStepWithNewSymbolDifferingFromSkolemizeTerm
    | SkolemizationStepWithoutBinding
    | SkolemizationStepWithoutNewSymbols
    | SkolemizationStepWithoutParent
    | SkolemizationStepWithMultipleParents
    | InferenceCycle
    | OtherFailureReason
    | StepWithInvalidStatus
    | StepWithInvalidInferenceRule
    | NegatedConjectureStepWithNonConjectureParent
    | NegatedConjectureWithoutParent
    | PlainInferenceWithConjectureParent
    | PlainInferenceWithoutSource
    | NegatedConjectureWithMultipleDistinctParents
    | DistinctFormulasWithSameName
    | NoRefutationFound
    | NonExistentStep
    | NonConstantSkolemTerm

type UnknownReason =
  Throwable
    | InputSyntaxError
    | CannotHandleInput
    | NoConjectureFound
    | UnexpectedInput
    | CannotHandleIncludeDirectives
    | FileNotFound

enum SzsStatus {
  case VerifiedGood
  case VerifiedBad(reason: VerifiedBadReason)
  case Unknown(reason: UnknownReason)
  case Timeout

  def status: String = this match {
    case VerifiedGood                                   => "VerifiedGood"
    case VerifiedBad(reason: TstpDerivationImportError) => s"VerifiedBad : ${reason.message}"
    case VerifiedBad(reason: OtherFailureReason)        => s"VerifiedBad : ${reason.toString}"
    case Unknown(_)                                     => "Unknown"
    case Timeout                                        => "Timeout"
  }
  def isGood: Boolean = this == VerifiedGood
  def isBad: Boolean = this.isInstanceOf[VerifiedBad]
  def isUnknown: Boolean = this.isInstanceOf[Unknown]

  def statusLine: String = s"% SZS status $status"
}

case class FileNotFound(fileName: String)
trait FileNameResolver {
  def apply(fileName: String): Either[FileNotFound, String]
}

object FileNameResolver {
  val empty: FileNameResolver = fileName => Left(FileNotFound(fileName))
  val absolute: FileNameResolver = fileName => {
    val path =
      if Paths.get(fileName).isAbsolute() then os.Path(fileName)
      else os.Path(fileName, os.pwd)

    if os.exists(path) then Right(os.read(path))
    else Left(FileNotFound(fileName))
  }
  given FileNameResolver = absolute
}

extension [R <: FileNameResolver](r: R) {
  def extend(f: FileNameResolver): FileNameResolver = fileName =>
    boundary { Right(f(fileName).getOrElse { r(fileName).getOrBreak }) }

  def relativeTo(root: os.Path): FileNameResolver = fileName =>
    if Paths.get(fileName).isAbsolute() then r(fileName)
    else r((root / os.RelPath(fileName)).toString)
}

val logger = Logger("time.checkTstpDerivation")

def checkTstpDerivation(file: InputFile, timeout: Duration = 25.seconds)(using resolver: FileNameResolver): SzsStatus = {
  logger.info(s"checking TSTP derivation ${file.fileName}")
  val input = resolver(file.fileName) match {
    case Left(e)      => return SzsStatus.Unknown(e)
    case Right(input) => input
  }
  val inputFile = InputFile.fromString(input)
  val result = {
    try withTimeout(timeout) {
        boundary {
          val derivation = logger.time("TstpDerivation.fromInputFile") {
            TstpDerivation.fromInputFile(inputFile).getOrBreak
          }
          val _ = derivation.nonConjectureRefutationLabels.headOption.getOrElse {
            break(Left(NoRefutationFound()))
          }
          logger.time("check file directives") {
            val memoTable: scala.collection.mutable.Map[String, TptpFile] = scala.collection.mutable.Map.empty
            derivation.stepsIterator.foreach {
              case step: (TstpAxiomStep | TstpConjectureStep) => {
                val fileDirectiveResolver = resolver.relativeTo(os.Path(file.fileName) / os.up)
                checkStepHasCorrectFileDirective(step)(using fileDirectiveResolver, memoTable).getOrBreak
              }
              case _ =>
            }
          }

          val usedNegatedConjectures = derivation.stepsIterator.collect { case s: TstpNegatedConjectureStep => s }
          usedNegatedConjectures.find(s => !s.hasUnambiguousStatusAmong(Set("cth"))).map { s =>
            break(Left(StepWithInvalidStatus(s.name, s.statuses, Set("cth"))))
          }

          val usedPlainInferences = derivation.stepsIterator.collect { case a: TstpPlainInferenceStep => a }
          usedPlainInferences.find(c => !c.hasUnambiguousStatusAmong(Set("thm"))).map { s =>
            break(Left(StepWithInvalidStatus(s.name, s.statuses, Set("thm"))))
          }

          val usedSkolemizationSteps = derivation.stepsIterator.collect { case s: TstpSkolemizationStep => s }
          usedSkolemizationSteps.find(s => !s.hasUnambiguousStatusAmong(Set("esa"))).map { s =>
            break(Left(StepWithInvalidStatus(s.name, s.statuses, Set("esa"))))
          }

          logger.time("tstpDerivationToProofContext") {
            checkIncorrectInferences(derivation)
          }
        }
      }
    catch e => Left(e)
  }

  result match {
    case Left(reason) => reason match {
        case _: TimeOutException => SzsStatus.Timeout
        case t: Throwable => {
          t.printStackTrace()
          SzsStatus.Unknown(t)
        }
        case r: UnknownReason          => SzsStatus.Unknown(r)
        case reason: VerifiedBadReason => SzsStatus.VerifiedBad(reason)
      }
    case Right(_) => SzsStatus.VerifiedGood
  }
}

private def checkStepHasCorrectFileDirective(
    s: TstpAxiomStep | TstpConjectureStep
)(using resolver: FileNameResolver, parseTptpMemoTable: scala.collection.mutable.Map[String, TptpFile]): Either[VerifiedBadReason, Unit] = boundary {
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

  val tptpFile = parseTptpMemoTable.getOrElseUpdate(
    fileName, {
      val tptpFileContent = resolver(fileName).getOrElse {
        break(Left(FileDirectiveFileNotFound(s.name, fileName)))
      }
      try TptpImporter.loadWithoutIncludes(InputFile.fromString(tptpFileContent))
      catch {
        case _: IllegalArgumentException =>
          break(Left(FileDirectiveInvalidSyntax(s.name, fileName)))
      }
    }
  )

  val fileDirectiveFormulas = tptpFile.inputs.collect {
    case a: AnnotatedFormula if a.name == label => a
  }
  val fileDirectiveFormula = fileDirectiveFormulas match {
    case Seq() =>
      break(Left(FileDirectiveFileDoesNotHaveLabel(s.name, fileName, label)))
    case Seq(_, _, _*) =>
      break(Left(FileDirectiveFileHasMultipleFormulasWithSameLabel(s.name, fileName, label)))
    case Seq(a @ AnnotatedFormula(language, name, "hypothesis", formula, annotations)) =>
      AnnotatedFormula(language, name, "axiom", formula, annotations) // hypothesis is a synonym for axiom
    case Seq(a) => a
  }

  if fileDirectiveFormula.role != s.role then {
    break(Left(FileDirectiveStepDoesNotMatchRole(s.name, fileName, label, s.role, fileDirectiveFormula.role)))
  }

  if !fileDirectiveFormula.formula.alphaEquals(s.formula) then {
    break(Left(FileDirectiveFormulaNotAlphaEquivalentToClaimedFormula(
      s.name,
      fileName,
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

extension (step: TstpDerivationStep) {
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

extension (step: TstpPlainInferenceStep) {
  def statuses: Set[String] = step.source.statuses
}

extension (step: TstpNegatedConjectureStep) {
  def statuses: Set[String] = step.source.statuses
}

extension (step: TstpSkolemizationStep) {
  def statuses: Set[String] = step.source.statuses
}
