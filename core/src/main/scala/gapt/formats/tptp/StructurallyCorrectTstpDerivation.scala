package gapt.formats.tptp.check

import gapt.expr.formula.Bottom
import gapt.formats.InputFile
import gapt.utils.linearizeStrictPartialOrder

import scala.util.boundary
import scala.util.boundary.break

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
    private val topologicallyOrderedFromSinksToSources: Iterable[String]
) {
  def stepsIterator: Iterator[ParsedTstpDerivationStep] = map.valuesIterator

  def stepsTopologicallyOrdered: Iterable[ParsedTstpDerivationStep] =
    topologicallyOrderedFromSinksToSources.map(map(_))

  def get(label: String): Option[ParsedTstpDerivationStep] = map.get(label)

  def parentsOf(formulaName: String): Seq[ParsedTstpDerivationStep] =
    map(formulaName).parents.map(map(_))

  val nonConjectureRootLabels: Set[String] = {
    def isRoot(key: String): Boolean =
      map(key).role != "conjecture" && map.forall((_, step) => !step.parents.contains(key))

    map.keys.filter(isRoot).toSet
  }

  val nonConjectureRefutationLabels: Set[String] =
    map.collect {
      case (label, step) if step.role != "conjecture" && step.formula == Bottom() => label
    }.toSet

  val nonConjectureRootRefutationLabels: Set[String] =
    nonConjectureRootLabels.intersect(nonConjectureRefutationLabels)

  private[check] def mapSteps(
      transform: ParsedTstpDerivationStep => ParsedTstpDerivationStep
  ): StructurallyCorrectTstpDerivation = {
    val transformedMap = map.map {
      case (label, step) =>
        val transformed = transform(step)
        require(transformed.name == step.name)
        require(transformed.parents == step.parents)
        require(transformed.getClass == step.getClass)
        label -> transformed
    }
    StructurallyCorrectTstpDerivation(transformedMap, topologicallyOrderedFromSinksToSources)
  }
}

object StructurallyCorrectTstpDerivation {
  def fromInputFile(
      input: InputFile
  ): Either[TstpDerivationError, StructurallyCorrectTstpDerivation] =
    ParsedTstpDerivation.fromInputFile(input).flatMap(fromParsed)

  def fromParsed(
      parsed: ParsedTstpDerivation
  ): Either[TstpDerivationError, StructurallyCorrectTstpDerivation] = {
    for
      map <- intoUniqueMap(parsed.steps)
      topologicalOrder <- sortTopologically(map)
      derivation = StructurallyCorrectTstpDerivation(map, topologicalOrder)
      _ <- checkRoleRelationships(derivation)
    yield derivation
  }

  private def checkRoleRelationships(
      derivation: StructurallyCorrectTstpDerivation
  ): Either[TstpDerivationError, Unit] = boundary {
    val negatedConjectures = derivation.stepsIterator.collect {
      case step: ParsedTstpNegatedConjectureStep => step
    }.toSeq
    negatedConjectures.find(step => derivation.parentsOf(step.name).exists(_.role != "conjecture")).foreach { step =>
      break(Left(NegatedConjectureStepWithNonConjectureParent(step.name)))
    }

    if negatedConjectures.size > 1 then
      break(Left(UnexpectedInput("got more than one negated conjecture")))

    derivation.stepsIterator.collect { case step: ParsedTstpPlainInferenceStep => step }
      .find(step => derivation.parentsOf(step.name).exists(_.role == "conjecture"))
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
