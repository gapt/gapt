package gapt.formats.tptp.check

import gapt.expr.Abs
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.formula.*
import gapt.expr.formula.Bottom
import gapt.expr.formula.Formula
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLFunction
import gapt.expr.formula.fol.FOLFunctionConst
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.hol.HOLPosition
import gapt.expr.given
import gapt.expr.substitute
import gapt.expr.ty.Ti
import gapt.expr.util.constants
import gapt.expr.util.freeVariables
import gapt.formats.InputFile
import gapt.formats.tptp.*
import gapt.formats.tptp.check.FindSkolemizableInstance.QuantifierType
import gapt.logic.Polarity
import gapt.logic.Polarity.Negative
import gapt.logic.Polarity.Positive
import gapt.logic.hol.SkolemFunctions
import gapt.proofs.Ant
import gapt.proofs.Sequent
import gapt.proofs.Suc
import gapt.proofs.context.Context
import gapt.proofs.context.State
import gapt.proofs.context.facet.ProofNames
import gapt.proofs.context.immutable.ImmutableContext
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.ProofDefinitionDeclaration
import gapt.proofs.context.update.ProofNameDeclaration
import gapt.proofs.context.update.Sort
import gapt.proofs.context.update.Update
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ExistsLeftRule
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ExistsSkLeftRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.ForallSkRightRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.ProofLink
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.provers.ResolutionProver
import gapt.provers.escargot.Escargot
import gapt.utils.Logger
import gapt.utils.Maybe
import gapt.utils.TimeOutException
import gapt.utils.getOrBreak
import gapt.utils.linearizeStrictPartialOrder
import gapt.utils.withTimeout

import java.nio.file.Paths
import java.util.concurrent.atomic.AtomicInteger
import scala.concurrent.Await
import scala.concurrent.ExecutionContext
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.concurrent.Promise
import scala.concurrent.duration.*
import scala.concurrent.duration.Duration
import scala.util.Failure
import scala.util.Success
import scala.util.boundary
import scala.util.boundary.Label
import scala.util.control.NonFatal

import boundary.break

type VerifiedBadReason =
  IncorrectInference
    | IncorrectSkolemization
    | SkolemizationStepWithNewSymbolDifferingFromSkolemizeTerm
    | SkolemizationStepWithoutBinding
    | SkolemizationStepWithoutNewSymbols
    | SkolemizationStepWithoutParent
    | SkolemizationStepWithMultipleParents
    | InferenceCycle
    | FileDirectiveError
    | StepWithInvalidStatus
    | StepWithInvalidInferenceRule
    | NegatedConjectureStepWithNonConjectureParent
    | NegatedConjectureWithoutParent
    | PlainInferenceWithConjectureParent
    | PlainInferenceWithoutSource
    | NegatedConjectureWithMultipleDistinctParents
    | DistinctFormulasWithSameName
    | NoRefutationFound
    | AmbiguousRefutationLabelsFound
    | NonExistentStep
    | NonConstantSkolemTerm

type VerifiedUnknownReason =
  UnexpectedException
    | InputSyntaxError
    | CannotHandleInput
    | NoConjectureFound
    | UnexpectedInput
    | CannotHandleIncludeDirectives
    | FileNotFound

enum SzsStatus {
  case VerifiedGood
  case VerifiedBad(reason: VerifiedBadReason)
  case Unknown(reason: VerifiedUnknownReason)
  case Timeout

  def status: String = this match {
    case VerifiedGood        => "VerifiedGood"
    case VerifiedBad(reason) => s"VerifiedBad : ${reason.message.replace("\n", "\\n")}"
    case Unknown(reason)     => s"Unknown : ${reason.message.replace("\n", "\\n")}"
    case Timeout             => "Timeout"
  }
  def isGood: Boolean = this == VerifiedGood
  def isBad: Boolean = this.isInstanceOf[VerifiedBad]
  def isUnknown: Boolean = this.isInstanceOf[Unknown]

  def statusLine: String = s"% SZS status $status"
}

sealed trait TstpDerivationStep {
  def name: String
  def role: String
  def formula: FOLFormula
  def parents: Seq[String]
}

case class TstpConjectureStep(
    name: String,
    formula: FOLFormula,
    annotationsOption: Option[Annotations]
) extends TstpDerivationStep {
  def parents: Seq[String] = Seq.empty
  def role: String = "conjecture"
}

case class TstpAxiomStep(
    name: String,
    formula: FOLFormula,
    annotationsOption: Option[Annotations]
) extends TstpDerivationStep {
  def parents: Seq[String] = Seq.empty
  def role: String = "axiom"
}

case class TstpPlainInferenceStep(
    name: String,
    formula: FOLFormula,
    parents: Seq[String],
    annotations: Annotations,
    source: Source.Inference
) extends TstpDerivationStep {
  def role: String = "plain"
}

case class TstpNegatedConjectureStep(
    name: String,
    formula: FOLFormula,
    parent: String,
    annotations: Annotations,
    source: Source.Inference
) extends TstpDerivationStep {
  def role: String = "negated_conjecture"
  def parents: Seq[String] = Seq(parent)
}

case class TstpSkolemizationStep(
    name: String,
    formula: FOLFormula,
    parent: String,
    source: Source.Inference,
    newSkolemSymbol: FOLFunctionConst,
    contextVariables: Seq[FOLVar],
    skolemizedSymbol: FOLVar,
    annotations: Annotations
) extends TstpDerivationStep {
  def parents: Seq[String] = Seq(parent)
  def role: String = "plain"
}

/**
* Represents all the information inside a TstpDerivation.
* It guarantees that the parent relationship is acyclic.
*/
case class TstpDerivation private (
    private val map: Map[String, TstpDerivationStep],
    private val topologicallyOrderedFromSinksToSources: Iterable[String]
) {
  def stepsIterator: Iterator[TstpDerivationStep] = map.valuesIterator
  def stepsTopologicallyOrdered: Iterable[TstpDerivationStep] = topologicallyOrderedFromSinksToSources.map(map(_))
  def get(label: String): Option[TstpDerivationStep] = map.get(label)

  def parentsOf(formulaName: String): Seq[TstpDerivationStep] = {
    map(formulaName).parents.map(p => map(p))
  }

  val nonConjectureRootLabels: Set[String] = {
    def isRoot(key: String): Boolean = {
      map(key).role != "conjecture" && map.forall((_, f) => !f.parents.contains(key))
    }

    map.keys.filter(isRoot).toSet
  }

  val nonConjectureRefutationLabels: Set[String] = {
    map.flatMap {
      case (k, f) if f.role != "conjecture" && f.formula == Bottom() => Some(k)
      case _                                                         => None
    }.toSet
  }

  val nonConjectureRootRefutationLabels: Set[String] =
    nonConjectureRootLabels.intersect(nonConjectureRefutationLabels)
}

object TstpDerivation {

  /** Loads a TstpDerivation from a given input file and performs the following checks, otherwise fails with an error:
  * - input is syntactically correct TPTP
  * - there are no steps with duplicate labels
  *
  * @param input
  * @return the TstpDerivation or an Error if there was an issue
  */
  def fromInputFile(input: InputFile): Either[TstpDerivationError, TstpDerivation] = {
    for
      tptp <- loadAsTptpFile(input)
      steps <- intoAnnotatedFormulaSteps(tptp)
      map <- intoUniqueMap(steps)
      checkedDerivation <- intoCheckedTstpDerivation(map)
    yield checkedDerivation
  }

  // ensures the input file is syntactically correct TPTP
  private def loadAsTptpFile(
      input: InputFile
  ): Either[InputSyntaxError, TptpFile] = {
    try Right(TptpImporter.loadWithoutIncludes(input))
    catch // In this case the input file was not valid TPTP
      case e: IllegalArgumentException => Left(InputSyntaxError(e))
  }

  // ensures that there are only AnnotatedFormula inputs
  private def intoAnnotatedFormulaSteps(
      tptpFile: TptpFile
  ): Either[CannotHandleIncludeDirectives, Seq[AnnotatedFormula]] = boundary {
    val formulas = tptpFile.inputs.map {
      case i: IncludeDirective =>
        break(Left(CannotHandleIncludeDirectives()))
      case a: AnnotatedFormula => a
    }
    Right(formulas)
  }

  // ensures there are no steps with duplicate labels
  private def intoUniqueMap(
      steps: Seq[AnnotatedFormula]
  ): Either[DistinctFormulasWithSameName, Map[String, AnnotatedFormula]] = boundary {
    val map = steps.foldLeft(Map.empty[String, AnnotatedFormula]) { (map, step) =>
      map.updatedWith(step.name) {
        case Some(formula) =>
          break(Left(DistinctFormulasWithSameName(formula.name)))

        case _ => Some(step)
      }
    }

    Right(map)
  }

  private def intoCheckedTstpDerivation(
      map: Map[String, AnnotatedFormula]
  ): Either[TstpDerivationError, TstpDerivation] = boundary {
    val topologicalOrder = sortTopologically(map).getOrBreak

    val steps = map.values.map { a => a.name -> parseStep(a).getOrBreak }.toMap

    val negatedConjectures = steps.values.collect { case s: TstpNegatedConjectureStep => s }
    negatedConjectures.find(c => map.hasNonConjectureParent(c.name)).map { s =>
      break(Left(NegatedConjectureStepWithNonConjectureParent(s.name)))
    }

    if negatedConjectures.size > 1 then {
      break(Left(UnexpectedInput("got more than one negated conjecture")))
    }

    val plainInferences = steps.values.collect { case a: TstpPlainInferenceStep => a }
    plainInferences.find(s => map.hasConjectureParent(s.name)).map { s =>
      break(Left(PlainInferenceWithConjectureParent(s)))
    }

    Right(TstpDerivation(steps, topologicalOrder))
  }

  private def sortTopologically(
      map: Map[String, AnnotatedFormula]
  ): Either[NonExistentStep | InferenceCycle, Iterable[String]] = boundary {
    import scala.collection.mutable

    val visited = mutable.Set[String]()
    val reachableSteps = mutable.Buffer[AnnotatedFormula]()
    def walk(label: String): Unit = {
      if !visited.contains(label) then {
        visited += label
        val formula = map.get(label).getOrElse {
          break(Left(NonExistentStep(label)))
        }
        reachableSteps += formula
        formula.parentLabels.foreach(walk)
      }
    }
    map.keysIterator.foreach(walk)

    val usedStepsRootToLeafs = linearizeStrictPartialOrder(reachableSteps.toSet, x => map.parentsOf(x.name)).getOrElse {
      break(Left(InferenceCycle()))
    }
    val usedStepsLeafsToRoot = usedStepsRootToLeafs.reverse

    Right(usedStepsLeafsToRoot.map(_.name))
  }

  private def parseStep(annotatedFormula: AnnotatedFormula): Either[TstpDerivationError, TstpDerivationStep] = boundary {
    val AnnotatedFormula(language, name, role, formula, annotations) = annotatedFormula
    language match {
      case "fof" | "cnf" => // we only support these languages for now
      case language =>
        break(Left(UnexpectedInput(s"unsupported input language $language. used in input $annotatedFormula")))
    }
    role match {
      case "axiom" | "hypothesis" =>
        parseAxiomStep(name, formula, annotations)
      case "conjecture" =>
        parseConjectureStep(name, formula, annotations)
      case "negated_conjecture" =>
        parseNegatedConjectureStep(name, formula, annotations)
      case "plain" =>
        parsePlainInferenceStep(name, formula, annotations)
      case r =>
        break(Left(UnexpectedInput(s"unsupported input role $r. used in input $annotatedFormula")))
    }
  }

  private def parseFOLFormula(formula: Formula): Either[TstpDerivationError, FOLFormula] = {
    if !formula.isInstanceOf[FOLFormula] then
      Left(UnexpectedInput(s"expected FOL formula, got ${formula.getClass}"))
    else
      Right(formula.asInstanceOf[FOLFormula])
  }

  private def parseAxiomStep(
      name: String,
      formula: Formula,
      annotations: Option[Annotations]
  ): Either[TstpDerivationError, TstpAxiomStep] = boundary {
    val fol = parseFOLFormula(formula).getOrBreak
    Right(TstpAxiomStep(name, fol, annotations))
  }

  private def parseConjectureStep(
      name: String,
      formula: Formula,
      annotations: Option[Annotations]
  ): Either[TstpDerivationError, TstpConjectureStep] = boundary {
    val fol = parseFOLFormula(formula).getOrBreak
    Right(TstpConjectureStep(name, fol, annotations))
  }

  private def parseNegatedConjectureStep(
      name: String,
      formula: Formula,
      annotationsOption: Option[Annotations]
  ): Either[TstpDerivationError, TstpNegatedConjectureStep] = boundary { l ?=>
    val folFormula = parseFOLFormula(formula).getOrBreak(using l)
    val annotations = annotationsOption.getOrElse {
      break(Left(UnexpectedInput("got negated conjecture without source")))
    }
    val inference = annotations.source match {
      case s: Source.Inference => s
      case _ =>
        break(Left(UnexpectedInput(s"got negated conjecture inference without inference record: $name")))
    }
    val expectedRule = "negated_conjecture"
    if inference.rule != expectedRule then
      break(Left(StepWithInvalidInferenceRule(name, inference.rule, expectedRule)))

    annotations.source.parentLabels.distinct match {
      case Seq() =>
        break(Left(NegatedConjectureWithoutParent(name)))
      case Seq(parent) =>
        Right(TstpNegatedConjectureStep(name, folFormula, parent, annotations, inference))
      case Seq(parent, _*) =>
        break(Left(NegatedConjectureWithMultipleDistinctParents()))
    }
  }

  private def parsePlainInferenceStep(
      name: String,
      formula: Formula,
      annotationsOption: Option[Annotations]
  ): Either[TstpDerivationError, TstpSkolemizationStep | TstpPlainInferenceStep] = boundary {
    val folFormula = parseFOLFormula(formula).getOrBreak
    val annotations = annotationsOption.getOrElse {
      break(Left(PlainInferenceWithoutSource(name)))
    }
    val inference = annotations.source match {
      case s: Source.Inference => s
      case s: Source.Internal  => break(Left(CannotHandleInput(name, "cannot handle internal sources")))
      case _                   => break(Left(PlainInferenceWithoutSource(name)))
    }

    val optionalInfo = annotations.optionalInfo
    inference.rule match {
      case "skolemize" => parseSkolemizationStep(name, folFormula, inference, optionalInfo)
      case _ =>
        Right(TstpPlainInferenceStep(
          name,
          folFormula,
          annotations.source.parentLabels,
          annotations,
          inference
        ))
    }
  }

  private def parseSkolemizationStep(
      name: String,
      formula: FOLFormula,
      inference: Source.Inference,
      optionalInfo: Seq[GeneralTerm]
  ): Either[TstpDerivationError, TstpSkolemizationStep] = boundary {
    val parent = inference.parentLabels match {
      case Seq()                   => break(Left(SkolemizationStepWithoutParent(name)))
      case parents @ Seq(_, _, _*) => break(Left(SkolemizationStepWithMultipleParents(name, parents)))
      case Seq(label)              => label
    }
    val newSkolemSymbols = inference.usefulInfo.collect {
      case TptpTerm("new_symbols", TptpTerm("skolem"), GeneralList(term: FOLConst)) => term
      case TptpTerm("new_symbols", TptpTerm("skolem"), GeneralList(term: FOLVar)) =>
        break(Left(NonConstantSkolemTerm(name, term)))
      case TptpTerm("new_symbols", TptpTerm("skolem"), GeneralList(term)) =>
        break(Left(CannotHandleInput(name, s"step $name: cannot handle new_symbols(skolem, term) if the term is complex. got term $term")))
      case TptpTerm("new_symbols", TptpTerm("skolem"), terms @ GeneralList(_, _*)) =>
        break(Left(CannotHandleInput(name, s"step $name: cannot handle multiple skolemizations in one step yet. got $terms")))
    }
    val newSkolemSymbol = newSkolemSymbols match {
      case Seq()         => break(Left(SkolemizationStepWithoutNewSymbols(name)))
      case Seq(_, _, _*) => break(Left(UnexpectedInput("expected at most one new_symbols(skolem,_) term")))
      case Seq(term)     => term.asInstanceOf[FOLConst]
    }
    val boundVariableSkolemTermPairs = inference.usefulInfo.collect {
      case TptpTerm("skolemize", boundVariable, skolemTerm: FOLTerm) => (boundVariable.asInstanceOf[FOLVar], skolemTerm)
    }
    val (boundVariable, skolemTerm) = boundVariableSkolemTermPairs match {
      case Seq()         => break(Left(SkolemizationStepWithoutBinding(name)))
      case Seq(_, _, _*) => break(Left(UnexpectedInput("expected at most one skolemize(_,_) term")))
      case Seq(pair)     => pair
    }
    val (skolemFunctionConst, args) = skolemTerm match {
      case FOLFunction(h, args) => (FOLFunctionConst(h, args.size), args)
      case _ =>
        break(Left(UnexpectedInput("expected skolem term to be a FOL term")))
    }
    val contextVariables = args.map {
      case x: FOLVar => x
      case _         => break(Left(UnexpectedInput("expected skolem term arguments to be first-order variables")))
    }
    if newSkolemSymbol.name != skolemFunctionConst.name then {
      break(Left(SkolemizationStepWithNewSymbolDifferingFromSkolemizeTerm(name)))
    }
    Right(TstpSkolemizationStep(
      name,
      formula,
      parent,
      inference,
      skolemFunctionConst,
      contextVariables,
      boundVariable,
      Annotations(inference, optionalInfo)
    ))
  }

  extension (map: Map[String, AnnotatedFormula]) {
    def parentsOf(label: String): Seq[AnnotatedFormula] = {
      map(label).parentLabels.map(p => map(p))
    }

    def hasNonConjectureParent(formulaName: String): Boolean = {
      map.parentsOf(formulaName).exists(p => p.role != "conjecture")
    }

    def hasConjectureParent(formulaName: String): Boolean = {
      map.parentsOf(formulaName).exists(p => p.role == "conjecture")
    }
  }
}

/**
* Checks if the given directed graph contains a cycle.
*
* @param nodes the set of nodes of the graph
* @param successors a function that returns for a given node in the graph the set of the nodes it can via a single edge
* @return true if the directed graph contains a cycle, false otherwise
*/
def isCyclic[T](nodes: Set[T], successors: T => Set[T]): Boolean = {
  linearizeStrictPartialOrder(nodes, successors).isLeft
}

extension [R <: FileNameResolver](r: R) {
  def extend(f: FileNameResolver): FileNameResolver = fileName =>
    boundary { Right(f(fileName).getOrElse { r(fileName).getOrBreak }) }

  def relativeTo(root: os.Path): FileNameResolver = fileName =>
    if Paths.get(fileName).isAbsolute() then r(fileName)
    else r((root / os.RelPath(fileName)).toString)
}

val logger = Logger("time.checkTstpDerivation")
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

          val negatedConjectures = derivation.stepsIterator.collect { case s: TstpNegatedConjectureStep => s }
          negatedConjectures.find(s => !s.hasUnambiguousStatusAmong(Set("cth"))).map { s =>
            break(Left(StepWithInvalidStatus(s.name, s.statuses, Set("cth"))))
          }

          val plainInferences = derivation.stepsIterator.collect { case a: TstpPlainInferenceStep => a }
          plainInferences.find(c => !c.hasUnambiguousStatusAmong(Set("thm"))).map { s =>
            break(Left(StepWithInvalidStatus(s.name, s.statuses, Set("thm"))))
          }

          val skolemizationSteps = derivation.stepsIterator.collect { case s: TstpSkolemizationStep => s }
          skolemizationSteps.find(s => !s.hasUnambiguousStatusAmong(Set("esa"))).map { s =>
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
          SzsStatus.Unknown(UnexpectedException(t))
        }
        case r: VerifiedUnknownReason  => SzsStatus.Unknown(r)
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

extension (annotatedFormula: AnnotatedFormula) {
  def parentLabels: Seq[String] = boundary {
    val annotations = annotatedFormula.annotations.getOrElse { break(Seq.empty) }
    annotations.source.parentLabels
  }
}

extension (source: Source) {
  def asInferenceOption: Option[Source.Inference] = source match {
    case s @ Source.Inference(rule, usefulInfo, parents) => Some(s)
    case _                                               => None
  }

  def parentLabels: Seq[String] = source match {
    case Source.Name(name)                                => Seq(name)
    case Source.Inference(_, _, parents)                  => parents.flatMap(_.source.parentLabels)
    case Source.Internal(_, _, parents)                   => parents.flatMap(_.source.parentLabels)
    case Source.File(_, _)                                => Seq.empty // for now we treat file sources as axioms that don't have parents
    case Source.Theory(_, _)                              => Seq.empty
    case Source.Creator(_, _, parents)                    => parents.flatMap(_.source.parentLabels)
    case Source.Unknown                                   => Seq.empty
    case Source.List(sources)                             => sources.flatMap(_.parentLabels)
    case Source.General(GeneralColon(TptpTerm(label), _)) => Seq(label)
    case Source.General(TptpTerm(dagSource))              => Seq(dagSource)
    case Source.General(term)                             => throw IllegalArgumentException(s"parent must be a simple term. got: $term")
  }
}

extension (step: TstpDerivationStep) {
  def annotationsOption: Option[Annotations] = step match {
    case s: TstpConjectureStep =>
      s.annotationsOption
    case s: TstpAxiomStep =>
      s.annotationsOption
    case s: TstpPlainInferenceStep =>
      Some(s.annotations)
    case s: TstpNegatedConjectureStep =>
      Some(s.annotations)
    case s: TstpSkolemizationStep =>
      Some(s.annotations)
  }
}

extension [T](a: IterableOnce[T]) {
  def single: T = a.iterator.take(2).toSeq match {
    case Seq()  => throw new NoSuchElementException
    case Seq(x) => x
    case _      => throw new IllegalArgumentException("Expected at most one element, got " + a)
  }

  def singleOption: Option[T] = a.iterator.take(2).toSeq match {
    case Seq()  => None
    case Seq(x) => Some(x)
    case _      => None
  }
}

case class VariableCapturingProofDeclaration(lhs: Expr, proof: LKProof) extends Update {
  def link = ProofLink(lhs, proof.endSequent)

  override def apply(ctx: Context): State =
    ctx + ProofNameDeclaration(lhs, proof.endSequent, freeVariables(proof.endSequent)) + ProofDefinitionDeclaration(lhs, proof) state

  override def toString: String =
    s"VariableCapturingProofDeclaration($lhs, ${proof.endSequent})"
}

/**
* Attempts to replay the inferences in the given TstpDerivation into a Context containing
* LKProofs for every inference step in the TstpDerivation
*/
def tstpDerivationToProofContext(
    derivation: TstpDerivation,
    prover: ResolutionProver = Escargot
): Either[IncorrectInference | IncorrectSkolemization, Context] = boundary { outer ?=>
  val (ctx, verifiedSkolemizationsByStepName) = constructTstpDerivationContext(derivation).getOrBreak
  given context: MutableContext = ctx.newMutable

  def addToContext(update: => Update) = {
    context += update
  }

  def replayProof(inferenceName: String, sequentToProve: Sequent[FOLFormula]): LKProof =
    logger.time(s"replaying proof step $inferenceName") {
      val replayContext = context
      prover.getLKProof(sequentToProve)(using replayContext).getOrElse {
        break(Left(IncorrectInference(inferenceName)))
      }
    }

  def proofDeclaration(name: String, proof: LKProof, parents: Seq[String]): VariableCapturingProofDeclaration = {
    val cutProof = parents.foldLeft(proof) { (proof, parent) =>
      val parentProofLink = context.get[ProofNames].link(FOLConst(parent)).get
      CutRule(parentProofLink, proof)
    }
    VariableCapturingProofDeclaration(FOLConst(name), cutProof)
  }

  def handleStep(s: TstpDerivationStep) = {
    s match {
      case _: TstpConjectureStep =>
      case s: TstpAxiomStep => {
        addToContext(proofDeclaration(s.name, LogicalAxiom(s.formula), Seq.empty))
      }

      case s: TstpNegatedConjectureStep => {
        val parentFormula = derivation.get(s.parent).get.formula

        // in the following we construct a proof of Neg(conjecture) :- s.formula
        // which is the only thing that is necessary for the refutation.
        // However, TSTP requires to check that the negated conjecture formula
        // is equivalent to the negation of the conjecture.
        // To represent this in the LKProof we construct a proof of
        // :- Neg(conjecture) <-> s.formula and cut it with a proof of
        // Neg(conjecture) <-> s.formula, Neg(conjecture) :- s.formula
        // which results from the proof of Neg(conjecture) :- s.formula by
        // weakening
        val negatedConjectureToFormulaProof =
          replayProof(s.name, Neg(parentFormula) +: Sequent() :+ s.formula)
        val formulaToNegatedConjectureProof =
          replayProof(s.name, s.formula +: Sequent() :+ Neg(parentFormula))
        val iffProof = AndRightRule(
          ImpRightRule(negatedConjectureToFormulaProof, Ant(0), Suc(0)),
          Suc(0),
          ImpRightRule(formulaToNegatedConjectureProof, Ant(0), Suc(0)),
          Suc(0)
        )
        val weakenedProof = WeakeningLeftRule(negatedConjectureToFormulaProof, iffProof.conclusion.succedent.head)
        val cutProof = CutRule(iffProof, weakenedProof)

        addToContext(proofDeclaration(s.name, cutProof, Seq.empty))
      }

      case s: TstpSkolemizationStep => {
        val skolemizationStep = verifiedSkolemizationsByStepName(s.name)
        addToContext(proofDeclaration(s.name, skolemizationStep.proof, Seq(s.parent)))
      }

      case s: TstpPlainInferenceStep => {
        val parentFormulas = s.parents.map(p => derivation.get(p).get.formula)
        val sequentToProve = Sequent(parentFormulas, Vector(s.formula))
        val proof = replayProof(s.name, sequentToProve)
        addToContext(proofDeclaration(s.name, proof, s.parents))
      }
    }
  }

  derivation.stepsTopologicallyOrdered.foreach(handleStep)

  Right(context.toImmutable)
}

def checkIncorrectInferences(
    derivation: TstpDerivation,
    prover: ResolutionProver = Escargot
): Either[IncorrectInference | IncorrectSkolemization, Unit] = boundary {
  val (ctx, verifiedSkolemizationsByStepName) = constructTstpDerivationContext(derivation).getOrBreak
  val context: MutableContext = ctx.newMutable

  def isValid(inferenceName: String, sequentToProve: Sequent[FOLFormula]): Boolean = {
    logger.time(s"replaying proof step $inferenceName") {
      val replayContext = context.newMutable
      prover.isValid(sequentToProve)(using replayContext)
    }
  }

  def firstCompletedMatching[A](input: Iterable[Future[A]])(predicate: A => Boolean): Future[Option[A]] = {
    val futures = input

    if futures.isEmpty then
      Future.successful(None)
    else {
      val result = Promise[Option[A]]()
      val remaining = new AtomicInteger(futures.size)

      def completedWithoutMatch(): Unit =
        if remaining.decrementAndGet() == 0 then
          result.trySuccess(None)

      futures.foreach { future =>
        future.onComplete {
          case Success(value) =>
            try {
              if predicate(value) then
                result.trySuccess(Some(value))
              else
                completedWithoutMatch()
            } catch {
              case NonFatal(error) =>
                result.tryFailure(error)
            }

          case Failure(e) =>
            result.tryFailure(e)
        }
      }

      result.future
    }
  }

  val futures: Seq[Future[(TstpDerivationStep, Boolean)]] = derivation.stepsIterator.toSeq.flatMap {
    case s: TstpPlainInferenceStep => {
      val parentFormulas = s.parents.map(p => derivation.get(p).get.formula)
      val sequentToProve = Sequent(parentFormulas, Vector(s.formula))
      Seq(Future {
        (s, isValid(s.name, sequentToProve))
      })
    }
    case s: TstpNegatedConjectureStep => {
      val parentFormula = derivation.get(s.parent).get.formula
      Seq(
        Future {
          val negatedConjectureToFormulaProof =
            isValid(s.name, Neg(parentFormula) +: Sequent() :+ s.formula)
          (s, negatedConjectureToFormulaProof)
        },
        Future {
          val formulaToNegatedConjectureProof =
            isValid(s.name, s.formula +: Sequent() :+ Neg(parentFormula))
          (s, formulaToNegatedConjectureProof)
        }
      )
    }
    case _ => Seq.empty
  }
  val incorrectStep = firstCompletedMatching(futures)((_, p) => !p)
  val result = Await.result(incorrectStep, Duration.Inf)
  result match {
    case None            => Right(())
    case Some((step, _)) => Left(IncorrectInference(step.name))
  }
}

private def constructTstpDerivationContext(
    derivation: TstpDerivation
): Either[IncorrectSkolemization, (ImmutableContext, Map[String, VerifiedSkolemization])] = boundary {
  val verifiedSkolemizationsByStepName = derivation.stepsIterator.collect {
    case step: TstpSkolemizationStep => {
      val parentFormula = derivation.get(step.parent).get.formula
      val locallyCorrectSkolemization =
        VerifiedSkolemization.fromTstpSkolemizationStepAndParentFormula(step, parentFormula).getOrBreak

      (step.name, locallyCorrectSkolemization)
    }
  }.toMap

  val verifiedSkolemDefinitions = ensureCompatibleSkolemDefinitions(verifiedSkolemizationsByStepName).getOrBreak

  val _ = ensureSkolemSymbolsDistinctFromInput(derivation, verifiedSkolemDefinitions).getOrBreak

  val context: MutableContext = MutableContext.default()
  context += Sort(Ti)

  def addConstantToContextIfNotPresent(c: Const): Unit = {
    if context.constant(c.name).isEmpty
    then context += c
  }

  derivation.stepsIterator.foreach { s =>
    constants.all(s.formula).foreach { c =>
      addConstantToContextIfNotPresent(c)
    }
  }
  verifiedSkolemDefinitions.foreach {
    case (_, (symbol, definition, _)) => {
      import gapt.proofs.context.facet.skolemFunsFacet
      addConstantToContextIfNotPresent(symbol)
      context += { ctx => ctx.state.update[SkolemFunctions](_ + (symbol, definition)) }
    }
  }

  Right((context.toImmutable, verifiedSkolemizationsByStepName))
}

type SkolemDefinition = Expr
type SkolemSymbol = FOLFunctionConst
type SkolemSymbolName = String
case class VerifiedSkolemization private (
    skolemSymbol: SkolemSymbol,
    skolemDefinition: SkolemDefinition,
    proof: LKProof
)

object VerifiedSkolemization {
  def fromTstpSkolemizationStepAndParentFormula(
      skolemizationStep: TstpSkolemizationStep,
      parentFormula: FOLFormula
  ): Either[IncorrectSkolemization, VerifiedSkolemization] =
    deepSkolemizationCheck(skolemizationStep, parentFormula)

  private def deepSkolemizationCheck(
      skolemizationStep: TstpSkolemizationStep,
      parentFormula: FOLFormula
  ) = boundary {
    val TstpSkolemizationStep(
      name,
      claimedSkolemizedFormula,
      parent,
      source,
      newSkolemSymbol,
      claimedContextVariables,
      claimedBoundVariable,
      _
    ) = skolemizationStep

    if claimedContextVariables.distinct != claimedContextVariables then {
      reportIncorrectSkolemization(NonRectifiedFormula(name, claimedSkolemizedFormula)) // TODO: find better error
    }

    val claimedSkolemTerm = newSkolemSymbol(claimedContextVariables*)
    val pol = Negative // TODO: we are assuming a negative context (i.e. if coming from an conjecture leaf, there was negated_conjecture before)
    val possibleMatches = FindSkolemizableInstance(parentFormula, claimedSkolemizedFormula, pol, claimedBoundVariable, newSkolemSymbol, claimedSkolemTerm)
    if possibleMatches.size == 0 then {
      reportIncorrectSkolemization(NoStrongQuantifierFittingSkolemization(name, parentFormula, claimedSkolemizedFormula, claimedBoundVariable, claimedSkolemTerm))
    }
    if possibleMatches.size > 1 then {
      reportIncorrectSkolemization(MultipleStrongQuantifiersFittingSkolemization(name, parentFormula, claimedSkolemizedFormula, claimedBoundVariable, claimedSkolemTerm))
    }
    val (quantifierPosition, skolemContext, parentContext) = possibleMatches(0)
    // TODO: get rid of cast
    val mainSkolemizationFormula = HOLPosition.toLambdaPosition(parentFormula)(quantifierPosition).get(parentFormula).get.asInstanceOf[FOLFormula]

    val (allContextQuantifierTypes, allContextVariables) = parentContext unzip
    val outerSkolemizationContextVariables = parentContext.collect { case (QuantifierType.Weak, x) => x.asInstanceOf[FOLVar] }

    val innerSkolemizationContextVariables = freeVariables(mainSkolemizationFormula).toSeq

    if allContextVariables.distinct != allContextVariables then {
      reportIncorrectSkolemization(NonRectifiedFormula(name, parentFormula))
    }

    if outerSkolemizationContextVariables.distinct != outerSkolemizationContextVariables then {
      reportIncorrectSkolemization(NonRectifiedFormula(name, parentFormula))
    }

    if outerSkolemizationContextVariables.contains(claimedBoundVariable) then {
      reportIncorrectSkolemization(NonRectifiedFormula(name, parentFormula))
    }

    if claimedContextVariables.toSet != outerSkolemizationContextVariables.toSet
      && claimedContextVariables.toSet != innerSkolemizationContextVariables.toSet
    then {
      reportIncorrectSkolemization(
        ContextVariableMismatch(
          name,
          claimedContextVariables,
          outerSkolemizationContextVariables,
          innerSkolemizationContextVariables,
          claimedBoundVariable,
          parentFormula
        )
      )
    }

    val skolemDefinition = Abs.Block(claimedContextVariables, mainSkolemizationFormula)

    val (parentSKVar, innerFormula) = mainSkolemizationFormula match {
      case All(v, f) => (v, f)
      case Ex(v, f)  => (v, f)
    }
    assert(parentSKVar == claimedBoundVariable, s"parentSKVar ($parentSKVar) does not match claimedBoundVariable ($claimedBoundVariable)")
    val inferredSkolemizationFormula = HOLPosition.replace(parentFormula, quantifierPosition, innerFormula.substitute(claimedBoundVariable -> claimedSkolemTerm)).asInstanceOf[FOLFormula]
    if inferredSkolemizationFormula != claimedSkolemizedFormula then {
      reportIncorrectSkolemization(FormulaMismatch(name, claimedSkolemizedFormula, claimedBoundVariable, claimedSkolemTerm, inferredSkolemizationFormula, parentFormula))
    }

    val skolemizationProof = CreateSkolemizationProof(parentFormula, inferredSkolemizationFormula, claimedBoundVariable, claimedSkolemTerm, innerFormula, quantifierPosition, pol)
    val cutWithClaimedFormula = CutRule(skolemizationProof, LogicalAxiom(claimedSkolemizedFormula)) // fixes alpha equivalence
    Right(new VerifiedSkolemization(newSkolemSymbol, skolemDefinition, cutWithClaimedFormula))
  }
}

private def ensureCompatibleSkolemDefinitions(
    skolemizationsByStepName: Map[String, VerifiedSkolemization]
): Either[IncorrectSkolemization, Map[String, (FOLFunctionConst, Expr, Set[String])]] = boundary {
  val skolemizationsBySkolemSymbolName =
    skolemizationsByStepName.groupBy((_, skolemization) => skolemization.skolemSymbol.name)

  val verifiedSkolemDefinitions = skolemizationsBySkolemSymbolName.map {
    case s @ (skolemSymbolName, definitionsByStepName) => {
      val incompatibilities = incompatibleSkolemDefinitions(definitionsByStepName)
      if incompatibilities.nonEmpty then {
        reportIncorrectSkolemization(MultipleIncompatibleSkolemDefinitionsOfSameSymbol(skolemSymbolName, incompatibilities))
      }

      val uniqueDefinitions = definitionsByStepName.map((_, skolemization) => (skolemization.skolemSymbol, skolemization.skolemDefinition)).toSet
      assert(uniqueDefinitions.size == 1, s"skolem symbol ${skolemSymbolName} has multiple incompatible definitions: $uniqueDefinitions")
      val (skolemConst, definition) = uniqueDefinitions.head
      val stepNames = definitionsByStepName.keySet
      (skolemSymbolName, (skolemConst, definition, stepNames))
    }
  }.toMap

  Right(verifiedSkolemDefinitions)
}

private def ensureSkolemSymbolsDistinctFromInput(
    derivation: TstpDerivation,
    verifiedSkolemDefinitions: Map[String, (FOLFunctionConst, Expr, Set[String])]
): Either[IncorrectSkolemization, Unit] = boundary {
  val inputSymbols = derivation.stepsIterator.collect {
    case s: TstpAxiomStep      => s.name -> constants.nonLogical(s.formula)
    case s: TstpConjectureStep => s.name -> constants.nonLogical(s.formula)
  }.toMap

  inputSymbols.foreach { (stepName, symbols) =>
    symbols.foreach { symbol =>
      verifiedSkolemDefinitions.get(symbol.name).foreach { (_, _, skolemizationStepNames) =>
        reportIncorrectSkolemization(SkolemSymbolIsAConstantExistingInTheInput(
          stepName,
          skolemizationStepNames.head,
          symbol
        ))
      }
    }
  }

  Right(())
}

private def incompatibleSkolemDefinitions(
    skolemizationsByStepName: Map[String, VerifiedSkolemization]
): Map[String, VerifiedSkolemization] = {
  skolemizationsByStepName.toSeq.combinations(2).foldLeft(Map.empty) {
    case (acc, Seq((leftStep, leftSkolemization), (rightStep, rightSkolemization))) => {
      val leftSymbol = leftSkolemization.skolemSymbol
      val rightSymbol = rightSkolemization.skolemSymbol
      assert(leftSymbol.name == rightSymbol.name, s"skolem symbol names do not match: ${leftSymbol.name} != ${rightSymbol.name}")
      acc ++ Set((leftStep, leftSkolemization), (rightStep, rightSkolemization))
    }
    case _ => throw new AssertionError("cannot happen as we only select 2 combinations")
  }
}

private def reportIncorrectSkolemization[T](
    reason: IncorrectSkolemizationReason
)(using Label[Left[IncorrectSkolemization, Nothing]]): Nothing =
  break(Left(IncorrectSkolemization(reason)))

object FindSkolemizableInstance {
  enum QuantifierType {
    case Strong
    case Weak
  }

  /**
   * Finds all positions p and variable contexts s.t. unskolemized[p] is a strongly quantified
   * formula Q skVar . F and replacing unskolemized[p] by F{skVar <- skTerm} obtains skolemized.
   */
  def apply(unskolemized: FOLFormula, skolemized: FOLFormula, polarity: Polarity, skVar: FOLVar, skConst: Const, skTerm: FOLTerm) = {
    def skQuantifier(e: Expr) = e match { case All(x, _) => skVar == x; case Ex(x, _) => skVar == x; case _ => false }
    val candidate_positions = HOLPosition.getPositions(unskolemized, skQuantifier)
    val qs = candidate_positions.filter(x => isStrongQuantifierPosition(x, unskolemized, polarity))
    // println(s"us: $unskolemized s: $skolemized candidates: $candidate_positions strong_qs: $qs")
    val correctly_skolemized = qs.filter(pos => {
      val inner_pos = HOLPosition(pos.list :+ 1)
      val lambda_pos = HOLPosition.toLambdaPosition(unskolemized)(inner_pos)
      val body = lambda_pos.get(unskolemized).get
      val reskolemized = HOLPosition.replace(unskolemized, pos, body.substitute(skVar -> skTerm))
//      println(s"$skolemized == $reskolemized")
      reskolemized == skolemized
    })
    def getContext(x: HOLPosition, f: FOLFormula) = polarityAndContextAt(x, f, polarity)._2
    correctly_skolemized.map(x => (x, getContext(x, skolemized), getContext(x, unskolemized)))
  }

  def polarityAndContextAt(pos: HOLPosition, e: Expr, polarity: Polarity, context: List[(QuantifierType, Var)] = Nil): (Polarity, List[(QuantifierType, Var)]) =
    (pos.list, e) match {
      case (Nil, _)           => (polarity, context.reverse)
      case (_, FOLAtom(_, _)) => (polarity, context.reverse)
      case (1 :: _, Neg(x))   => polarityAndContextAt(pos.tail, x, !polarity, context)
      case (1 :: _, All(v, x)) =>
        val ws = if polarity == Positive then QuantifierType.Strong else QuantifierType.Weak
        polarityAndContextAt(pos.tail, x, polarity, (ws, v) :: context)
      case (1 :: _, Ex(v, x)) =>
        val ws = if polarity == Positive then QuantifierType.Weak else QuantifierType.Strong
        polarityAndContextAt(pos.tail, x, polarity, (ws, v) :: context)
      case (1 :: _, And(x, _)) => polarityAndContextAt(pos.tail, x, polarity, context)
      case (2 :: _, And(_, x)) => polarityAndContextAt(pos.tail, x, polarity, context)
      case (1 :: _, Or(x, _))  => polarityAndContextAt(pos.tail, x, polarity, context)
      case (2 :: _, Or(_, x))  => polarityAndContextAt(pos.tail, x, polarity, context)
      case (1 :: _, Imp(x, _)) => polarityAndContextAt(pos.tail, x, !polarity, context)
      case (2 :: _, Imp(_, x)) => polarityAndContextAt(pos.tail, x, polarity, context)
      case _                   => throw new Exception(s"Could not find polarity of $pos in $e")
    }

  def isStrongQuantifierPosition(pos: HOLPosition, e: Expr, polarity: Polarity): Boolean = {
    val pol = polarityAndContextAt(pos, e, polarity)._1
    val lambda_pos = HOLPosition.toLambdaPosition(e)(pos)
    lambda_pos.get(e) match {
      case Some(All(_, _)) => pol == Positive
      case Some(Ex(_, _))  => pol == Negative
      case _               => false
    }
  }
}

object CreateSkolemizationProof {

  /**
   * creates a proof F :- skF
   * @param unskolemized the unskolemized formula F
   * @param skolemized the skolemized formula skF
   * @param skVar the variable of the strong quantifier removed
   * @param skTerm the skolem term
   * @param pathToSk the position at which the strong quantifier occurs
   * @param polarity in which polarity we are right now
   * @return
   */
  def apply(unskolemized: FOLFormula, skolemized: FOLFormula, skVar: FOLVar, skTerm: FOLTerm, innerFormula: FOLFormula, pathToSk: HOLPosition, polarity: Polarity): LKProof = {
    if unskolemized == skolemized then
      LogicalAxiom(skolemized)
    if pathToSk.isEmpty then {
      val innerSubstituted = innerFormula.substitute(skVar -> skTerm)
      val axiom = LogicalAxiom(innerSubstituted)
      if polarity == Negative then
        ExistsSkLeftRule(axiom, Ant(0), Ex(skVar, innerFormula), skTerm)
      else
        ForallSkRightRule(axiom, Suc(0), All(skVar, innerFormula), skTerm)
    } else {
      val branch = pathToSk.head
      val remainingBranch = pathToSk.tail
      // polarity swaps on which side the unskolemized and skolemized formula appear (neg: skolemized right, pos: skolemized left)
      def swapPos(a: FOLFormula, b: FOLFormula) = if polarity == Negative then (a, b) else (b, a)

      (unskolemized, skolemized, branch) match {
        case (a @ Neg(f), sa @ Neg(fs), 1) =>
          val rp = apply(f, fs, skVar, skTerm, innerFormula, remainingBranch, !polarity)
          val (b, sb) = swapPos(fs, f) // NegLeftRule needs the auxiliary, not the primary formula
          val p1 = NegLeftRule(rp, sb)
          NegRightRule(p1, b)
        case (a @ And(f, g), sa @ And(fs, _), 1) =>
          val rp = apply(f, fs, skVar, skTerm, innerFormula, remainingBranch, polarity)
          val axiom = LogicalAxiom(g)
          val (b, sb) = swapPos(a, sa)
          val p1 = AndRightRule(rp, axiom, sb)
          AndLeftRule(p1, b)
        case (a @ And(f, g), sa @ And(_, gs), 2) =>
          val axiom = LogicalAxiom(f)
          val rp = apply(g, gs, skVar, skTerm, innerFormula, remainingBranch, polarity)
          val (b, sb) = swapPos(a, sa)
          val p1 = AndRightRule(axiom, rp, sb)
          AndLeftRule(p1, b)
        case (a @ Or(f, g), sa @ Or(fs, _), 1) =>
          val rp = apply(f, fs, skVar, skTerm, innerFormula, remainingBranch, polarity)
          val axiom = LogicalAxiom(g)
          val (b, sb) = swapPos(a, sa)
          val p1 = OrLeftRule(rp, axiom, b)
          OrRightRule(p1, sb)
        case (a @ Or(f, g), sa @ Or(_, gs), 2) =>
          val rp = apply(g, gs, skVar, skTerm, innerFormula, remainingBranch, polarity)
          val axiom = LogicalAxiom(f)
          val (b, sb) = swapPos(a, sa)
          val p1 = OrLeftRule(axiom, rp, b)
          OrRightRule(p1, sb)
        case (a @ Imp(f, g), sa @ Imp(fs, _), 1) =>
          val rp = apply(f, fs, skVar, skTerm, innerFormula, remainingBranch, !polarity)
          val axiom = LogicalAxiom(g)
          val (b, sb) = swapPos(a, sa)
          val p1 = ImpLeftRule(rp, axiom, b)
          ImpRightRule(p1, sb)
        case (a @ Imp(f, g), sa @ Imp(_, gs), 2) =>
          val rp = apply(g, gs, skVar, skTerm, innerFormula, remainingBranch, polarity)
          val axiom = LogicalAxiom(f)
          val (b, sb) = swapPos(a, sa)
          val p1 = ImpLeftRule(axiom, rp, b)
          ImpRightRule(p1, sb)
        case (a @ All(x, f), All(y, fs), 1) =>
          val sa = All(x, fs)
          val rp = apply(f, fs, skVar, skTerm, innerFormula, remainingBranch, polarity)
          val (b, sb) = swapPos(a, sa)
          val p1 = ForallLeftRule(rp, b)
          ForallRightRule(p1, sb)
        case (a @ Ex(x, f), sa @ Ex(y, fs), 1) =>
          val rp = apply(f, fs, skVar, skTerm, innerFormula, remainingBranch, polarity)
          val (b, sb) = swapPos(a, sa)
          val p1 = ExistsRightRule(rp, sb)
          ExistsLeftRule(p1, b)
        case _ =>
          throw IllegalArgumentException(s"Unhandled case ($unskolemized, $skolemized, $pathToSk, $polarity)")
      }
    }
  }
}

sealed trait TstpDerivationError {
  def message: String
}

case class InputSyntaxError(
    cause: IllegalArgumentException
) extends TstpDerivationError {
  override def message: String = cause.getMessage
}

case class DistinctFormulasWithSameName(
    label: String
) extends TstpDerivationError {
  override def message: String = s"there are multiple distinct formulas with the same name: $label"
}

case class InferenceCycle() extends TstpDerivationError {
  def message: String = "inference cycle detected"
}

case class StepWithInvalidStatus(
    stepName: String,
    actualStatuses: Iterable[String],
    validStatuses: Iterable[String]
) extends TstpDerivationError {
  override def message: String = s"$stepName has invalid statuses ${actualStatuses.mkString(", ")}. Expected one of ${validStatuses.mkString(", ")}"
}

case class StepWithInvalidInferenceRule(
    stepName: String,
    actualInferenceName: String,
    expectedInferenceName: String
) extends TstpDerivationError {
  override def message: String = s"$stepName has invalid inference name '$actualInferenceName'. Expected '$expectedInferenceName'"
}

case class NegatedConjectureStepWithNonConjectureParent(
    stepName: String
) extends TstpDerivationError {
  def message: String = s"step with name $stepName has a non-conjecture parent"
}

case class NegatedConjectureWithoutParent(
    stepName: String
) extends TstpDerivationError {
  def message: String = s"negated conjecture step with name $stepName has no parent"
}

case class NegatedConjectureWithMultipleDistinctParents() extends TstpDerivationError {
  def message: String = "got negated conjecture with multiple distinct parents"
}

case class PlainInferenceWithConjectureParent(
    step: TstpPlainInferenceStep
) extends TstpDerivationError {
  def message: String = s"plain inference step with name ${step.name} has a conjecture parent"
}

case class PlainInferenceWithoutSource(
    stepName: String
) extends TstpDerivationError {
  def message: String = s"plain inference step with name $stepName has no source"
}

case class IncorrectInference(
    stepName: String
) extends TstpDerivationError {
  def message: String = s"inference step with name $stepName is incorrect"
}

case class IncorrectSkolemization(
    reason: IncorrectSkolemizationReason
) extends TstpDerivationError {
  def message: String = reason.message
}

case class NonConstantSkolemTerm(
    stepName: String,
    term: FOLVar
) extends TstpDerivationError {
  def message: String = s"step $stepName: skolem term $term is not a constant, but a variable"
}

case class SkolemizationStepWithoutParent(
    stepName: String
) extends TstpDerivationError {
  def message: String = s"skolemization inference with name $stepName has no parent"
}

case class SkolemizationStepWithMultipleParents(
    stepName: String,
    parents: Seq[String]
) extends TstpDerivationError {
  def message: String = s"skolemization inference with name $stepName has multiple parents ${parents.mkString(", ")}"
}

case class NonExistentStep(
    stepName: String
) extends TstpDerivationError {
  def message: String = s"step with name $stepName does not exist"
}

sealed trait IncorrectSkolemizationReason {
  def message: String
}

case class NoExistentialQuantifierAfterRootUniversalBlock(
    stepName: String,
    claimedBoundVariable: FOLVar,
    innerFormula: FOLFormula,
    parentFormula: FOLFormula
) extends IncorrectSkolemizationReason {
  def message: String = s"skolemization step $stepName claims to skolemize bound variable $claimedBoundVariable, but there is no existential quantifier following after the outermost universal quantifiers. got $innerFormula inside universal quantifier block of parent formula $parentFormula"
}

case class BoundVariableMismatch(
    stepName: String,
    claimedBoundVariable: FOLVar,
    actualBoundVariable: FOLVar,
    parentFormula: FOLFormula
) extends IncorrectSkolemizationReason {
  def message: String = s"skolemization step $stepName claims to skolemize bound variable $claimedBoundVariable, but the actual outer most existential variable in $parentFormula is $actualBoundVariable"
}

case class ContextVariableMismatch(
    stepName: String,
    claimedContextVariables: Seq[FOLVar],
    actualOuterSkolemizationContextVariables: Seq[FOLVar],
    actualInnerSkolemizationContextVariables: Seq[FOLVar],
    claimedBoundVariable: FOLVar,
    parentFormula: FOLFormula
) extends IncorrectSkolemizationReason {
  def message: String = s"skolemization step $stepName claims to have context variables $claimedContextVariables, but this neither matches the actual outer skolemization context variables ($actualOuterSkolemizationContextVariables) nor the inner skolemization context variables ($actualInnerSkolemizationContextVariables) for $claimedBoundVariable in $parentFormula"
}

case class FormulaMismatch(
    stepName: String,
    claimedSkolemizedFormula: FOLFormula,
    claimedBoundVariable: FOLVar,
    claimedSkolemTerm: FOLTerm,
    expectedSkolemizedFormula: FOLFormula,
    parentFormula: FOLFormula
) extends IncorrectSkolemizationReason {
  def message: String = s"skolemization step $stepName claims to skolemize formula $parentFormula by replacing $claimedBoundVariable with $claimedSkolemTerm which should result in $expectedSkolemizedFormula but the given formula is $claimedSkolemizedFormula"
}

case class MultipleIncompatibleSkolemDefinitionsOfSameSymbol(
    skolemSymbol: String,
    stepDefinitions: Map[String, VerifiedSkolemization]
) extends IncorrectSkolemizationReason {
  def message: String = s"skolem symbol $skolemSymbol is introduced multiple times with conflicting definitions: ${stepDefinitions.map { case (step, skolemization) => s"in $step defined as skolem symbol ${skolemization.skolemSymbol} with ${skolemization.skolemDefinition}" }.mkString("; ")}"
}

case class SkolemSymbolIsAConstantExistingInTheInput(
    inputStepName: String,
    skolemizationStepName: String,
    const: Const
) extends IncorrectSkolemizationReason {
  def message: String = s"skolemization step $skolemizationStepName introduces skolem symbol $const that is already used in the input in step $inputStepName"
}

case class NonRectifiedFormula(
    stepName: String,
    formula: FOLFormula
) extends IncorrectSkolemizationReason {
  def message: String = s"skolemization step $stepName has non-rectified parent formula $formula (contains different quantifiers with the same bound variable)"
}

case class SkolemizationStepWithNewSymbolDifferingFromSkolemizeTerm(
    stepName: String
) extends TstpDerivationError {
  def message: String = s"skolemization step with name $stepName has differing skolem terms"
}

case class SkolemizationStepWithoutNewSymbols(
    stepName: String
) extends TstpDerivationError {
  def message: String = s"skolemization step with name $stepName has no new symbols"
}

case class SkolemizationStepWithoutBinding(
    stepName: String
) extends TstpDerivationError {
  def message: String = s"skolemization step with name $stepName has no skolemize(_,_) binding"
}

case class CannotHandleIncludeDirectives() extends TstpDerivationError {
  def message: String = "cannot handle include directives"
}

case class CannotHandleInput(stepName: String, reason: String) extends TstpDerivationError {
  def message: String = s"cannot handle input step with name $stepName: $reason"
}

case class NoRefutationFound() extends TstpDerivationError {
  def message: String = "no refutation found as there is no unique $false formula in the derivation"
}

case class AmbiguousRefutationLabelsFound(labels: Seq[String]) extends TstpDerivationError {
  def message: String = s"no refutation found as there are multiple $$false formulas in the derivation: ${labels.mkString(", ")}"
}

case class NoConjectureFound() extends TstpDerivationError {
  def message: String = s"no conjecture found: $message"
}

case class UnexpectedInput(message: String) extends TstpDerivationError

case class NoStrongQuantifierFittingSkolemization(stepName: String, inputFormula: FOLFormula, skolemizedFormula: FOLFormula, skVar: FOLVar, skTerm: FOLTerm)
    extends IncorrectSkolemizationReason {
  def message: String = s"could not find a strong quantifier s.t. replacing $skVar with $skTerm transforms $inputFormula into $skolemizedFormula!"
}

case class MultipleStrongQuantifiersFittingSkolemization(stepName: String, inputFormula: FOLFormula, skolemizedFormula: FOLFormula, skVar: FOLVar, skTerm: FOLTerm)
    extends IncorrectSkolemizationReason {
  def message: String = s"could find multiple (non-unique) strong quantifiers s.t. replacing $skVar with $skTerm transforms $inputFormula into $skolemizedFormula!"
}

sealed trait FileDirectiveError extends TstpDerivationError
case class SourceMissing(stepName: String) extends FileDirectiveError {
  override def message: String = s"step $stepName is missing a source"
}

case class FileDirectiveMissing(stepName: String) extends FileDirectiveError {
  override def message: String = s"step $stepName is missing a file directive"
}

case class FileDirectiveLabelMissing(stepName: String) extends FileDirectiveError {
  override def message: String = s"step $stepName is missing a file directive label"
}

case class FileDirectiveFileNotFound(stepName: String, fileName: String) extends FileDirectiveError {
  override def message: String = s"step $stepName has a file source (${fileName}) that could not be found"
}

case class FileDirectiveInvalidSyntax(stepName: String, fileName: String) extends FileDirectiveError {
  override def message: String = s"step $stepName has a file source (${fileName}) with invalid TPTP syntax"
}

case class FileDirectiveFileDoesNotHaveLabel(
    stepName: String,
    fileName: String,
    label: String
) extends FileDirectiveError {
  override def message: String = s"step $stepName has a file source (${fileName}) that does not have the label '$label'"
}

case class FileDirectiveFileHasMultipleFormulasWithSameLabel(
    stepName: String,
    fileName: String,
    label: String
) extends FileDirectiveError {
  override def message: String = s"step $stepName has a file source (${fileName}) that has multiple distinct formulas with the same label '$label'"
}

case class FileDirectiveStepDoesNotMatchRole(
    stepName: String,
    fileName: String,
    label: String,
    expectedRole: String,
    actualRole: String
) extends FileDirectiveError {
  override def message: String = s"step ${stepName} has a file source (${fileName}) that points to a formula with name ${label} that does not have the same role as the step. expected: ${expectedRole}, actual: ${actualRole}"
}

case class FileDirectiveFormulaNotAlphaEquivalentToClaimedFormula(
    stepName: String,
    fileName: String,
    label: String,
    expected: Formula,
    actual: Formula
) extends FileDirectiveError {
  override def message: String = s"step ${stepName} has a file source (${fileName}) that points to a formula with name ${label} that is not alpha-equivalent to the claimed formula. expected: ${expected}, actual: ${actual}"
}

case class FileNotFound(fileName: String) extends TstpDerivationError {
  override def message: String = s"file not found: $fileName"
}

case class UnexpectedException(e: Throwable) extends TstpDerivationError {
  override def message: String = s"unexpected exception: ${e.getMessage}"
}
