package gapt.formats.tptp.check

import gapt.expr.Expr
import gapt.expr.formula.Bottom
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.util.constants
import gapt.formats.InputFile
import gapt.formats.tptp.*
import gapt.utils.{NameGenerator, getOrBreak, linearizeStrictPartialOrder}

import scala.util.boundary
import scala.util.boundary.break

private[check] case class NamedTptpInputFile(fileName: String, content: String) extends InputFile {
  override def read: String = content
}

private[check] enum TptpFileLoadingError {
  case FileNotFound(fileName: String)
  case InvalidSyntax(fileName: String)
  case IncludeCycle(fileName: String)
}

private[check] def loadTptpFileWithIncludes(
    inputFile: InputFile
)(using resolver: FileNameResolver): Either[TptpFileLoadingError, TptpFile] = {
  def go(
      filePath: os.Path,
      content: String,
      includedFiles: Set[os.Path]
  ): Either[TptpFileLoadingError, Seq[AnnotatedFormula]] = boundary {
    val parsed =
      try TptpImporter.loadWithoutIncludes(InputFile.fromString(content))
      catch {
        case _: IllegalArgumentException => break(Left(TptpFileLoadingError.InvalidSyntax(filePath.toString)))
      }

    val inputs = parsed.inputs.flatMap {
      case a: AnnotatedFormula => Seq(a)
      case IncludeDirective(includedFileName, selection) =>
        val currentDirectory = filePath / os.up
        val resolvedPath = os.Path(includedFileName, currentDirectory)
        if includedFiles.contains(resolvedPath) then
          break(Left(TptpFileLoadingError.IncludeCycle(resolvedPath.toString)))

        val includedContent = resolver(resolvedPath.toString).getOrElse {
          break(Left(TptpFileLoadingError.FileNotFound(resolvedPath.toString)))
        }
        val includedFile = go(
          resolvedPath,
          includedContent,
          includedFiles + resolvedPath
        ).getOrBreak
        includedFile.filter {
          case AnnotatedFormula(_, name, _, _, _) => selection.forall(_.contains(name))
        }
    }

    Right(inputs)
  }

  val inputPath = os.Path(inputFile.fileName, os.pwd)
  go(inputPath, inputFile.read, Set(inputPath))
    .map(TptpFile(_))
}

/**
 * A parsed TSTP derivation whose parent relation is structurally well-formed.
 *
 * In particular, step labels are unique, every parent label denotes a step,
 * and the parent relation is acyclic.  The derivation therefore also provides
 * an ordering in which every parent occurs before its children.  It also
 * guarantees that there is at most one negated conjecture, that a negated
 * conjecture has only conjecture parents, and that plain inferences do not
 * have conjecture parents.
 */
final class StructurallyCorrectTstpDerivation private[check] (
    private val map: Map[String, ParsedTstpDerivationStep],
    private val topologicallyOrderedFromSinksToSources: Iterable[String],
    private val labelsInSourceOrder: Seq[String]
) {
  def stepsIterator: Iterator[ParsedTstpDerivationStep] = map.valuesIterator

  def stepsInSourceOrderIterator: Iterator[ParsedTstpDerivationStep] =
    labelsInSourceOrder.iterator.map(map(_))

  def stepsTopologicallyOrdered: Iterable[ParsedTstpDerivationStep] =
    topologicallyOrderedFromSinksToSources.map(map(_))

  def get(label: String): Option[ParsedTstpDerivationStep] = map.get(label)

  def parentsOf(formulaName: String): Seq[ParsedTstpDerivationStep] =
    map(formulaName).parents.map(map(_))

  val nonConjectureRootLabels: Set[String] = {
    val referencedLabels = map.valuesIterator.flatMap(_.parents).toSet
    labelsInSourceOrder.iterator
      .filter(label => map(label).role != TstpRole.Conjecture && !referencedLabels.contains(label))
      .toSet
  }

  val nonConjectureRefutationLabels: Set[String] =
    map.collect {
      case (label, step) if step.role != TstpRole.Conjecture && step.formula == Bottom() => label
    }.toSet

  val nonConjectureRootRefutationLabels: Set[String] =
    nonConjectureRootLabels.intersect(nonConjectureRefutationLabels)

}

object StructurallyCorrectTstpDerivation {
  private[check] def deoverloadSymbols(
      derivation: StructurallyCorrectTstpDerivation
  ): StructurallyCorrectTstpDerivation = {
    val constantsInSourceOrder = derivation.labelsInSourceOrder.iterator
      .map(derivation.map(_))
      .flatMap(step => constants.all(step.formula))
      .toSeq
      .distinct
    val constantsByName = constantsInSourceOrder.groupBy(_.name)
    val nameGenerator = new NameGenerator(constantsByName.keys)
    val renamingTable = constantsByName.toSeq.sortBy(_._1).flatMap { (symbolName, symbols) =>
      if symbols.size == 1 then
        Seq(symbols.head -> symbolName)
      else
        Seq(symbols.head -> symbolName) ++
          symbols.tail.map(symbol => symbol -> nameGenerator.freshWithIndex(symbolName))
    }.toMap

    def renamedFormula(formula: FOLFormula): FOLFormula =
      renameConsts(renamingTable)(formula).asInstanceOf[FOLFormula]

    def renamedTerm(term: Expr): Expr = renameConsts(renamingTable)(term)

    def renamedSource(source: Source): Source = source match {
      case Source.Name(name) => Source.Name(name)
      case Source.Inference(rule, usefulInfo, parents) =>
        Source.Inference(
          rule,
          usefulInfo.map(renamedTerm),
          parents.map(parent => parent.copy(source = renamedSource(parent.source), details = parent.details.map(renamedTerm)))
        )
      case Source.Internal(introType, usefulInfo, parents) =>
        Source.Internal(
          introType,
          usefulInfo.map(renamedTerm),
          parents.map(parent => parent.copy(source = renamedSource(parent.source), details = parent.details.map(renamedTerm)))
        )
      case Source.File(fileName, fileInfo) => Source.File(fileName, fileInfo)
      case Source.Theory(name, usefulInfo) => Source.Theory(name, usefulInfo.map(renamedTerm))
      case Source.Creator(name, usefulInfo, parents) =>
        Source.Creator(
          name,
          usefulInfo.map(renamedTerm),
          parents.map(parent => parent.copy(source = renamedSource(parent.source), details = parent.details.map(renamedTerm)))
        )
      case Source.Unknown       => Source.Unknown
      case Source.List(sources) => Source.List(sources.map(renamedSource))
      case Source.General(term) => Source.General(renamedTerm(term))
    }

    def renamedAnnotations(annotations: Annotations): Annotations =
      annotations.copy(
        source = renamedSource(annotations.source),
        optionalInfo = annotations.optionalInfo.map(renamedTerm)
      )

    def renamedStep(step: ParsedTstpDerivationStep): ParsedTstpDerivationStep = step match {
      case step: ParsedTstpAxiomStep      => step.copy(formula = renamedFormula(step.formula))
      case step: ParsedTstpConjectureStep => step.copy(formula = renamedFormula(step.formula))
      case step: ParsedTstpNegatedConjectureStep =>
        val annotations = renamedAnnotations(step.annotations)
        step.copy(
          formula = renamedFormula(step.formula),
          annotations = annotations
        )
      case step: ParsedTstpPlainInferenceStep =>
        val annotations = renamedAnnotations(step.annotations)
        step.copy(
          formula = renamedFormula(step.formula),
          annotations = annotations
        )
      case step: ParsedTstpSkolemizationStep =>
        val annotations = renamedAnnotations(step.annotations)
        step.copy(
          formula = renamedFormula(step.formula),
          newSkolemSymbol = renamedTerm(step.newSkolemSymbol).asInstanceOf[gapt.expr.formula.fol.FOLFunctionConst],
          annotations = annotations
        )
    }

    val renamedMap = derivation.map.view.mapValues(renamedStep).toMap
    new StructurallyCorrectTstpDerivation(
      renamedMap,
      derivation.topologicallyOrderedFromSinksToSources,
      derivation.labelsInSourceOrder
    )
  }

  def fromInputFile(input: InputFile)(using resolver: FileNameResolver): Either[TstpDerivationError, StructurallyCorrectTstpDerivation] =
    loadTptpFileWithIncludes(input).left.map {
      case TptpFileLoadingError.FileNotFound(fileName)  => IncludeFileNotFound(fileName)
      case TptpFileLoadingError.InvalidSyntax(fileName) => IncludeInvalidSyntax(fileName)
      case TptpFileLoadingError.IncludeCycle(fileName)  => IncludeCycle(fileName)
    }.flatMap(tptpFile => ParsedTstpDerivation.parseTptpFile(tptpFile).flatMap(fromParsed))

  def fromParsed(
      parsed: ParsedTstpDerivation
  ): Either[TstpDerivationError, StructurallyCorrectTstpDerivation] = {
    for
      map <- intoUniqueMap(parsed.steps)
      topologicalOrder <- sortTopologically(map)
      derivation = StructurallyCorrectTstpDerivation(map, topologicalOrder, parsed.steps.map(_.name))
      _ <- checkRoleRelationships(derivation)
    yield derivation
  }

  private def checkRoleRelationships(
      derivation: StructurallyCorrectTstpDerivation
  ): Either[TstpDerivationError, Unit] = boundary {
    val negatedConjectures = derivation.stepsInSourceOrderIterator.collect {
      case step: ParsedTstpNegatedConjectureStep => step
    }.toSeq
    val conjectures = derivation.stepsInSourceOrderIterator.collect {
      case step: ParsedTstpConjectureStep => step
    }.toSeq

    if conjectures.size > 1 then
      break(Left(MultipleConjectures(conjectures.map(_.name))))

    negatedConjectures.find(step => derivation.parentsOf(step.name).exists(_.role != TstpRole.Conjecture)).foreach { step =>
      break(Left(NegatedConjectureStepWithNonConjectureParent(step.name)))
    }

    if negatedConjectures.size > 1 then
      break(Left(UnexpectedInput("got more than one negated conjecture")))

    derivation.stepsInSourceOrderIterator.filter(_.role == TstpRole.Plain)
      .find(step => derivation.parentsOf(step.name).exists(_.role == TstpRole.Conjecture))
      .foreach { step =>
        break(Left(PlainInferenceWithConjectureParent(step)))
      }

    Right(())
  }

  private def intoUniqueMap(
      steps: Seq[ParsedTstpDerivationStep]
  ): Either[DistinctFormulasWithSameName, Map[String, ParsedTstpDerivationStep]] = boundary {
    val map = steps.foldLeft(Map.empty[String, ParsedTstpDerivationStep]) { (map, step) =>
      map.updatedWith(step.name) {
        case Some(formula) =>
          break(Left(DistinctFormulasWithSameName(formula.name)))
        case None => Some(step)
      }
    }

    Right(map)
  }

  private def sortTopologically(
      map: Map[String, ParsedTstpDerivationStep]
  ): Either[NonExistentStep | InferenceCycle, Iterable[String]] = boundary {
    import scala.collection.mutable

    val visited = mutable.Set[String]()
    val reachableSteps = mutable.Buffer[ParsedTstpDerivationStep]()
    def walk(label: String): Unit = {
      if !visited.contains(label) then {
        visited += label
        val formula = map.get(label).getOrElse {
          break(Left(NonExistentStep(label)))
        }
        reachableSteps += formula
        formula.parents.foreach(walk)
      }
    }
    map.keysIterator.foreach(walk)

    val orderedFromChildrenToParents =
      linearizeStrictPartialOrder(reachableSteps.toSet, step => parentsOf(map, step.name)).getOrElse {
        break(Left(InferenceCycle()))
      }

    Right(orderedFromChildrenToParents.reverse.map(_.name))
  }

  private def parentsOf(
      map: Map[String, ParsedTstpDerivationStep],
      label: String
  ): Seq[ParsedTstpDerivationStep] = map(label).parents.map(map(_))
}
