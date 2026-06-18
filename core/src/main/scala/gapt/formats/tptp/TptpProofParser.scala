package gapt.formats.tptp

import gapt.expr._
import gapt.expr.formula.And
import gapt.expr.formula.Bottom
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.hol.{containsStrongQuantifier, universalClosure}
import gapt.expr.util.freeVariables
import gapt.formats.InputFile
import gapt.logic.Polarity
import gapt.logic.clauseSubsumption
import gapt.logic.hol.CNFn
import gapt.logic.hol.CNFp
import gapt.proofs.resolution.{AvatarDefinition, AvatarGroundComp, AvatarNonGroundComp, AvatarSplit}
import gapt.proofs.sketch._
import gapt.proofs.{FOLClause, HOLSequent, Sequent}

import scala.collection.mutable
import scala.util.boundary
import scala.util.Try

enum InferenceStatus {
  case Thm
  case Cth
  case Esa
}

enum TptpProofImportError {
  case InputSyntaxError
  case DifferentFormulasWithSameName
  case InferenceCycle
  case NegatedConjectureWithInvalidStatus
  case NegatedConjectureWithNonConjectureParent
  case NegatedConjectureWithoutParent
  case PlainInferenceWithInvalidStatus
  case PlainInferenceWithConjectureParent
  case IncorrectNegatedConjectureInference
  case IncorrectPlainInference
}

case class TptpRefutationSketch(
    val refutationSketch: RefutationSketch,
    // this is None if the negated conjecture is not used in the refutation sketch
    val conjectureNegatedConjecturePair: Option[(Formula, Formula)]
)

/**
 * Represents a malformed input file e.g. one that contains an unknown parent step
 */
class MalformedInputFileException(s: String) extends IllegalArgumentException(s)

case class TptpInferenceRecord(val name: String, val usefulInfo: Seq[GeneralTerm], val parents: Seq[String])

extension (inference: TptpInferenceRecord) {
  def statuses: Seq[InferenceStatus] = {
    inference.usefulInfo.collect {
      case TptpTerm("status", TptpTerm(s)) => s match {
          case "thm" => InferenceStatus.Thm
          case "cth" => InferenceStatus.Cth
          case "esa" => InferenceStatus.Esa
        }
    }
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

case class TptpProofMap private (private val map: Map[String, AnnotatedFormula]) extends Map[String, AnnotatedFormula] {
  export map.*
}

object TptpProofMap {
  def apply(steps: Seq[AnnotatedFormula]): Try[TptpProofMap] = Try {
    val map = scala.collection.mutable.Map[String, AnnotatedFormula]()
    for s <- steps do {
      map.updateWith(s.name) {
        case Some(formula) if s != formula =>
          throw IllegalArgumentException(
            s"""formula $formula with name ${formula.name} is already present.
               |Attempted to add another formula $s with the same name.""".stripMargin
          )
        case _ => Some(s)
      }
    }

    new TptpProofMap(map.toMap)
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
    case Source.General(term)                             => throw IllegalArgumentException(s"cannot get parent labels of term: $term")
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

  def parents: Set[String] = boundary {
    val annotations = annotatedFormula.annotations.getOrElse {
      boundary.break(Set.empty)
    }
    val parentInfos = annotations.source match {
      case Source.Inference(rule, usefulInfo, parents)     => parents
      case Source.Internal(introType, usefulInfo, parents) => parents
      case Source.Creator(name, usefulInfo, parents)       => parents
      case Source.List(sources) =>
        throw new UnsupportedOperationException("cannot get parents of alternative list sources")

      case Source.Name(name)               => Set.empty
      case Source.File(fileName, fileInfo) => Set.empty
      case Source.Theory(name, usefulInfo) => Set.empty
      case Source.Unknown                  => Set.empty
      case Source.General(term)            => Set.empty
    }

    parentInfos.map {
      case ParentInfo(Source.Name(name), _) => name
      case _ =>
        throw new UnsupportedOperationException("cannot get non-name parent")
    }.toSet
  }
}

case class TptpProofDag private (private val map: Map[String, AnnotatedFormula]) extends Map[String, AnnotatedFormula] {
  export map.*

  def parentsOf(formulaName: String): Set[AnnotatedFormula] = {
    map(formulaName).parents.map(p => map(p))
  }

  def ancestorsOf(formulaName: String): Set[AnnotatedFormula] = {
    val formula = map(formulaName)
    val parents = formula.parents.map(p => map(p))
    parents ++ parents.flatMap(p => ancestorsOf(p.name))
  }

  def isUsedInDerivationOf(used: String, derivationOf: String): Boolean = {
    used == derivationOf || ancestorsOf(derivationOf).exists(_.name == used)
  }

  def hasNonConjectureParent(formulaName: String): Boolean = {
    parentsOf(formulaName).exists(p => p.role != "conjecture")
  }

  def hasConjectureParent(formulaName: String): Boolean = {
    parentsOf(formulaName).exists(p => p.role == "conjecture")
  }
}

object TptpProofDag {
  def apply(map: TptpProofMap): Try[TptpProofDag] = Try {
    if isCyclic(map.keySet, n => map(n).parents) then
      throw IllegalArgumentException(s"Cycle detected in proof starting from node ${map.keySet.head}")
    else new TptpProofDag(map.toMap)
  }
}

def isCyclic[T](nodes: Set[T], neighbors: T => Set[T]): Boolean = {
  val visited = scala.collection.mutable.Set[T]()
  def isPartOfCycle(node: T, path: Seq[T] = Seq.empty): Boolean = {
    if path.contains(node) then return true
    if visited.contains(node) then return false
    visited.add(node)
    neighbors(node).exists(p => isPartOfCycle(p, path :+ node))
  }

  nodes.exists(n => isPartOfCycle(n))
}

object TptpProofParser {
  def parseTptpRefutationSketch(file: InputFile): Either[TptpProofImportError, TptpRefutationSketch] = boundary {
    val tptpFile = {
      try TptpImporter.loadWithoutIncludes(file)
      catch
        // In this case the input file was not valid TPTP
        case _: IllegalArgumentException => boundary.break(Left(TptpProofImportError.InputSyntaxError))
    }

    val annotatedFormulaSteps = tptpFile.inputs.map {
      case i @ IncludeDirective(_, _) =>
        throw UnsupportedOperationException(s"cannot handle include directive when checking proof. got $i")
      case a @ AnnotatedFormula(_, _, _, _, _) => a
    }

    val tptpProofMap = TptpProofMap(annotatedFormulaSteps).getOrElse {
      boundary.break(Left(TptpProofImportError.DifferentFormulasWithSameName))
    }
    val tptpProofDag = TptpProofDag(tptpProofMap).getOrElse {
      boundary.break(Left(TptpProofImportError.InferenceCycle))
    }

    val claimedNegatedConjectures = tptpProofDag.values.collect {
      case a @ AnnotatedFormula(_, _, "negated_conjecture", _, _) => a
    }
    if claimedNegatedConjectures.exists(c => !c.hasUnambiguousStatusAmong(Set("cth"))) then {
      boundary.break(Left(TptpProofImportError.NegatedConjectureWithInvalidStatus))
    }
    if claimedNegatedConjectures.exists(c => tptpProofDag.hasNonConjectureParent(c.name)) then {
      boundary.break(Left(TptpProofImportError.NegatedConjectureWithNonConjectureParent))
    }
    if claimedNegatedConjectures.exists(c => tptpProofDag.parentsOf(c.name).isEmpty) then {
      boundary.break(Left(TptpProofImportError.NegatedConjectureWithoutParent))
    }

    val plainInferences = tptpProofDag.values.collect {
      case a @ AnnotatedFormula(_, _, "plain", _, _) => a
    }
    if plainInferences.exists(c => !c.hasUnambiguousStatusAmong(Set("thm", "esa"))) then {
      boundary.break(Left(TptpProofImportError.PlainInferenceWithInvalidStatus))
    }
    if plainInferences.exists(c => tptpProofDag.hasConjectureParent(c.name)) then {
      boundary.break(Left(TptpProofImportError.PlainInferenceWithConjectureParent))
    }

    val (_, sketch) = parse(file)

    val refutationHead = tptpProofDag.values.collect {
      case a @ AnnotatedFormula(_, _, _, Bottom(), _) => a
    }.single
    val usedNegatedConjectures = tptpProofDag.values.collect {
      case a @ AnnotatedFormula(_, _, "negated_conjecture", _, _)
          if tptpProofDag.isUsedInDerivationOf(a.name, refutationHead.name) => a
    }

    if usedNegatedConjectures.isEmpty then
      return Right(TptpRefutationSketch(sketch, None))

    if usedNegatedConjectures.size > 1 then
      throw new IllegalArgumentException(s"Expected exactly one negated conjecture used in the refutation sketch, got ${usedNegatedConjectures.size}")

    val negatedConjecture = usedNegatedConjectures.head
    val conjectures = tptpFile.inputs.collect {
      case a @ AnnotatedFormula(_, _, "conjecture", _, _) => a
    }
    val conjecture = conjectures.head
    Right(TptpRefutationSketch(sketch, Some((conjecture.formula, negatedConjecture.formula))))
  }

  def parse(out: InputFile, labelledCNF: Map[String, Seq[FOLClause]]): RefutationSketch =
    parseSteps(TptpImporter.loadWithoutIncludes(out), labelledCNF)

  def removeStrongQuants(tptpFile: TptpFile): TptpFile = {
    val stepsWithStrongQuants = tptpFile.inputs.filter {
      case AnnotatedFormula(_, _, _, _, Some(Annotations(Source.Internal(sat_splitting, _, _), _))) if sat_splitting.startsWith("sat_splitting") =>
        false
      case AnnotatedFormula(_, _, _, _, Some(Annotations(Source.Internal(avatar, _, _), _))) if avatar.startsWith("AVATAR") =>
        false
      case AnnotatedFormula(_, _, _, _, Some(Annotations(Source.Internal(avatar, _, _), _))) if avatar.startsWith("avatar") =>
        false
      case AnnotatedFormula(_, _, "conjecture", formula, _) =>
        containsStrongQuantifier(formula, Polarity.InSuccedent)
      case AnnotatedFormula(_, _, _, formula, _) =>
        containsStrongQuantifier(formula, Polarity.InAntecedent)
      case _ => false
    }.collect { case f: AnnotatedFormula => f.name }.toSet
    if (stepsWithStrongQuants.isEmpty)
      tptpFile
    else
      TptpFile(tptpFile.inputs.collect { case f: AnnotatedFormula if !stepsWithStrongQuants(f.name) => f }.map {
        case f @ AnnotatedFormula(_, _, _, _, Some(Annotations(source, _))) if source.parentLabels.toSet.intersect(stepsWithStrongQuants).isEmpty => f
        case AnnotatedFormula(_, label, "conjecture", formula, _) =>
          AnnotatedFormula("fof", label, "conjecture", formula, None)
        case f => AnnotatedFormula("fof", f.name, "axiom", f.formula, None)
      })
  }

  def parse(out: InputFile, ignoreStrongQuants: Boolean = false): (Sequent[FOLFormula], RefutationSketch) = {
    var tptpFile = TptpImporter.loadWithoutIncludes(out)
    if (ignoreStrongQuants) tptpFile = removeStrongQuants(tptpFile)
    val (endSequent, labelledCNF) = extractEndSequentAndCNF(tptpFile)
    endSequent -> parseSteps(tptpFile, labelledCNF)
  }

  def extractEndSequentAndCNF(stepList: TptpFile): (Sequent[FOLFormula], Map[String, Seq[FOLClause]]) = {
    var endSequent = Sequent[FOLFormula]()
    val labelledCNF = mutable.Map[String, Seq[FOLClause]]().withDefaultValue(Seq())

    def addAsCNFAxioms(language: String, label: String, formula: FOLFormula): Unit = {
      endSequent +:= (if (language == "cnf") universalClosure(formula) else formula)
      labelledCNF(label) ++= CNFp(formula).toSeq
    }

    stepList.inputs.foreach {
      case AnnotatedFormula("fof", label, "conjecture", formula: FOLFormula, _) =>
        endSequent :+= formula
        labelledCNF(label) ++= CNFn(formula).toSeq
      case AnnotatedFormula(language, _, "plain", formula: FOLFormula, Some(Annotations(Source.File(_, Some(label)), _))) =>
        // for now we add file sources as axioms without checking whether
        // the file being referred to actually contains the formula as an axiom
        addAsCNFAxioms(language, label, formula)
      case AnnotatedFormula(lang, label, "axiom" | "negated_conjecture" | "hypothesis", formula: FOLFormula, _) =>
        addAsCNFAxioms(lang, label, formula)
      case _ =>
    }

    endSequent -> labelledCNF.toMap
  }

  def findClauseRenaming(from: HOLSequent, to: HOLSequent): Option[Map[Var, Var]] =
    if (from.sizes != to.sizes)
      None
    else for {
      subst <- clauseSubsumption(from, to)
      // FIXME: this would only be correct if we considered all subsumptions...
      if subst.isInjectiveRenaming
    } yield subst.map.map { case (l, r) => l -> r.asInstanceOf[Var] }

  def parseSteps(stepList: TptpFile, labelledCNF: Map[String, Seq[FOLClause]]): RefutationSketch = {
    val steps = (for (case input @ AnnotatedFormula(_, name, _, _, _) <- stepList.inputs)
      yield name -> input).toMap

    val memo = mutable.Map[String, Seq[RefutationSketch]]()
    val alreadyVisited = mutable.Set[String]()
    val splDefs = mutable.Map[(FOLAtom, Boolean), AvatarDefinition]()
    val splAtoms = mutable.Set[FOLAtom]()

    def filterVampireSplits(clause: FOLClause): FOLClause = clause.filterNot(splAtoms)

    def convertAvatarDefinition(defn: Formula, splAtom: FOLAtom): Seq[RefutationSketch] = {
      splAtoms += splAtom
      val comps = defn match {
        case splAtom @ FOLAtom(_, _) if freeVariables(splAtom).isEmpty =>
          Polarity.values.map {
            AvatarGroundComp(splAtom, _)
          }
        case Neg(splAtom @ FOLAtom(_, _)) if freeVariables(splAtom).isEmpty =>
          Polarity.values.map {
            AvatarGroundComp(splAtom, _)
          }
        case _ =>
          Seq(AvatarNonGroundComp(splAtom, AvatarNonGroundComp.DefinitionFormula.canonize(defn)))
      }
      comps.map { comp =>
        splDefs((splAtom, comp.assertion.succedent.nonEmpty)) = comp
        SketchComponentIntro(comp)
      }
    }

    def haveAlreadyVisited(stepName: String): Boolean = {
      val res = alreadyVisited(stepName)
      alreadyVisited += stepName
      res
    }

    def convert(stepName: String): Seq[RefutationSketch] = {
      val step = steps.getOrElse(stepName, throw new MalformedInputFileException(s"unknown step $stepName"))

      def convertSat_splitting_refutationBottomInference(source: Source): Seq[SketchSplitCombine] = {
        val sketchParents = source.parentLabels.flatMap(convert)
        val splitParents = sketchParents.map { parent0 =>
          var parent = parent0
          for {
            clauseComponent <- AvatarSplit.getComponents(parent0.conclusion)
            comp <- splDefs.values
            renaming <- findClauseRenaming(comp.clause, clauseComponent)
          } parent = SketchComponentElim(
            parent,
            comp match {
              case comp @ AvatarNonGroundComp(_, _, vars) => comp.copy(vars = vars.map(renaming))
              case AvatarGroundComp(_, _)                 => comp
            }
          )
          require(parent.conclusion.isEmpty)
          parent
        }
        Seq(SketchSplitCombine(splitParents))
      }

      def convertAVATAR_split_clauseInference(disj: Formula, source: Source): Seq[RefutationSketch] = {
        val Seq(assertion) = CNFp(disj).toSeq
        val Seq(splittedClause, _*) = source.parentLabels.flatMap(convert): @unchecked

        var p = splittedClause
        for {
          clauseComponent <- AvatarSplit.getComponents(splittedClause.conclusion)
          case (splAtom: FOLAtom, i) <- assertion.zipWithIndex
          comp <- splDefs.get((splAtom, i.isSuc))
          renaming <- findClauseRenaming(comp.clause, clauseComponent)
        } p = SketchComponentElim(
          p,
          comp match {
            case comp @ AvatarNonGroundComp(_, _, vars) => comp.copy(vars = vars.map(renaming))
            case AvatarGroundComp(_, _)                 => comp
          }
        )

        require(p.conclusion.isEmpty, s"$assertion\n$splittedClause\n$splDefs")
        Seq(p)
      }

      def convertAVATAR_sat_refutationInference(source: Source): Seq[SketchSplitCombine] = {
        Seq(SketchSplitCombine(source.parentLabels.flatMap(convert)))
      }

      def convertRemainingCases(conclusion: FOLFormula, source: Source): Seq[RefutationSketch] = {
        CNFp(conclusion).toSeq match {
          case Seq(conclusionClause) =>
            val sketchParents = source.parentLabels.flatMap(convert)
            val conclusionClause_ = filterVampireSplits(conclusionClause)
            val sketchParents_ = sketchParents.find(p => clauseSubsumption(p.conclusion, conclusionClause_).isDefined).fold(sketchParents)(Seq(_))
            Seq(SketchInference(conclusionClause_, sketchParents_))
          case clauses => source.parentLabels.flatMap(convert)
        }
      }

      memo.getOrElseUpdate(
        stepName,
        (step: @unchecked) match {
          case _ if haveAlreadyVisited(stepName) =>
            throw new IllegalArgumentException(s"Cyclic inference: ${steps(stepName)}")
          case AnnotatedFormula("fof", _, "plain", And(Imp(defn, Neg(splAtom: FOLAtom)), _), Some(Annotations(Source.Internal("sat_splitting_component", _, _), _))) =>
            convertAvatarDefinition(defn, splAtom)

          case AnnotatedFormula(
                "fof",
                _,
                "plain",
                Bottom(),
                Some(
                  Annotations(
                    source @ Source.Inference("sat_splitting_refutation", _, _),
                    _
                  )
                )
              ) => {
            convertSat_splitting_refutationBottomInference(source)
          }

          case AnnotatedFormula(
                "fof",
                _,
                "plain",
                And(Imp(splAtom: FOLAtom, defn), _),
                Some(Annotations(Source.Internal("AVATAR_definition" | "avatar_definition", _, _), _))
              ) =>
            convertAvatarDefinition(defn, splAtom)
          case AnnotatedFormula(
                "fof",
                _,
                "plain",
                disj,
                Some(Annotations(source @ Source.Inference("AVATAR_split_clause" | "avatar_split_clause", _, _), _))
              ) =>
            convertAVATAR_split_clauseInference(disj, source)
          case AnnotatedFormula(
                "fof",
                _,
                "plain",
                Bottom(),
                Some(Annotations(
                  justification @ Source.Inference(
                    "AVATAR_sat_refutation" | "avatar_sat_refutation" | "avatar_smt_refutation",
                    _,
                    _
                  ),
                  _
                ))
              ) =>
            convertAVATAR_sat_refutationInference(justification)
          case AnnotatedFormula("fof", label, "conjecture", _, _) =>
            labelledCNF(label).map(SketchAxiom.apply)
          case AnnotatedFormula(_, _, "plain", axiom: FOLFormula, Some(Annotations(Source.File(_, Some(label)), _))) =>
            // we treat plain inferences from file sources as axioms for now without checking
            labelledCNF(label).map(SketchAxiom.apply)
          case AnnotatedFormula(_, label, "axiom" | "negated_conjecture" | "hypothesis", axiom: FOLFormula, _)
              // sometimes provers add an axiom that wasn't directly part of the input, but
              // they add this axiom as a new name that only refers to an existing axiom that
              // was part of the input problem. in that case labelledCNF wouldn't contain this
              // axiom, so this case will fall through to the next.
              // for now this means that we treat such axioms just like ordinary plain inferences
              if labelledCNF.contains(label) => {
            CNFp(axiom).toSeq match {
              case Seq(axiomClause) =>
                Seq(SketchInference(
                  axiomClause,
                  labelledCNF(label).map(SketchAxiom.apply)
                ))
              case clauses => labelledCNF(label).map(SketchAxiom.apply)
            }
          }
          case AnnotatedFormula(_, _, _, conclusion: FOLFormula, Some(Annotations(source, _))) => {
            convertRemainingCases(conclusion, source)
          }
        }
      )
    }

    val emptyClauseLabel = stepList.inputs.collect {
      case AnnotatedFormula(_, label, _, Bottom(), _) => label
    }.head
    convert(emptyClauseLabel).head

  }
}
