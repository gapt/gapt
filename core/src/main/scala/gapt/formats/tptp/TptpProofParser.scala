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
import gapt.utils.getOrBreak

import scala.collection.mutable
import scala.util.boundary
import boundary.break
import scala.util.boundary.Label
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.fol.FOLFunction
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLFunctionConst

sealed trait TptpDerivationStep {
  def formula: FOLFormula
  def name: String
}
case class TptpConjectureStep(name: String, formula: FOLFormula, annotationsOption: Option[Annotations]) extends TptpDerivationStep
case class TptpAxiomStep(name: String, formula: FOLFormula, annotationsOption: Option[Annotations]) extends TptpDerivationStep
case class TptpPlainInferenceStep(name: String, formula: FOLFormula, parents: Seq[String], annotations: Annotations) extends TptpDerivationStep
case class TptpNegatedConjectureStep(name: String, formula: FOLFormula, parent: String, annotations: Annotations) extends TptpDerivationStep
case class TptpSkolemizationStep(
    name: String,
    formula: FOLFormula,
    parent: String,
    newSkolemSymbol: FOLFunctionConst,
    contextVariables: Seq[FOLVar],
    skolemizedSymbol: FOLVar,
    annotations: Annotations
) extends TptpDerivationStep

sealed trait TptpDerivationImportError {
  def message: String
}
case class InputSyntaxError(cause: IllegalArgumentException) extends TptpDerivationImportError {
  override def message: String = cause.getMessage
}
case class DifferentFormulasWithSameName(message: String) extends TptpDerivationImportError
case class InferenceCycle(message: String) extends TptpDerivationImportError
case class StepWithInvalidStatus(message: String, step: TptpDerivationStep) extends TptpDerivationImportError
case class NegatedConjectureStepWithNonConjectureParent(message: String) extends TptpDerivationImportError
case class NegatedConjectureWithoutParent(message: String) extends TptpDerivationImportError
case class PlainInferenceWithConjectureParent(message: String, step: TptpPlainInferenceStep) extends TptpDerivationImportError
case class IncorrectInference(message: String, step: TptpDerivationStep) extends TptpDerivationImportError

case class SkolemizationStepWithDifferingSkolemTerms(message: String, stepName: String) extends TptpDerivationImportError

case class CannotHandleInput(message: String, stepName: String | TptpInput) extends TptpDerivationImportError
case class NoRefutationFound(message: String) extends TptpDerivationImportError
case class NoConjectureFound(message: String) extends TptpDerivationImportError
case class UnexpectedInput(message: String) extends TptpDerivationImportError

/**
* Represents all the information inside a TptpDerivation.
* It guarantees that the parent relationship is acyclic.
*/
case class TptpDerivation private (private val map: Map[String, AnnotatedFormula]) {
  def annotatedFormulas: Iterable[AnnotatedFormula] = map.values

  def get(label: String): Option[AnnotatedFormula] = map.get(label)

  def parentsOf(formulaName: String): Seq[AnnotatedFormula] = {
    map(formulaName).parentLabels.map(p => map(p))
  }

  def subDerivationRootedAt(derivationEndLabel: String): Iterable[AnnotatedFormula] = {
    import scala.collection.mutable
    val visited = mutable.Set[String]()
    val queue = mutable.Queue[String](derivationEndLabel)
    val steps = mutable.Buffer[AnnotatedFormula]()
    while queue.nonEmpty do {
      val element = queue.dequeue()
      if !visited.contains(element) then {
        visited += element
        steps += map(element)
        queue ++= map(element).parentLabels
      }
    }
    steps
  }
}

object TptpDerivation {

  /** Loads a TptpDerivation from a given input file and performs the following checks, otherwise fails with an error:
  * - input is syntactically correct TPTP
  * - there are not steps with duplicate labels
  * - the parent relation between inference steps forms an acyclic directed graph
  *
  * @param input
  * @return the TptpDerivation or an Error if there was an issue
  */
  def fromInputFile(input: InputFile): Either[TptpDerivationImportError, TptpDerivation] = {
    for
      tptp <- loadAsTptpFile(input)
      steps <- intoAnnotatedFormulaSteps(tptp)
      m <- intoUniqueMap(steps)
      dag <- intoDag(m)
    yield dag
  }

  // ensures the input file is syntactically correct TPTP
  private def loadAsTptpFile(input: InputFile): Either[InputSyntaxError, TptpFile] = {
    try Right(TptpImporter.loadWithoutIncludes(input))
    catch // In this case the input file was not valid TPTP
      case e: IllegalArgumentException => Left(InputSyntaxError(e))
  }

  // ensures that there are only AnnotatedFormula inputs
  private def intoAnnotatedFormulaSteps(tptpFile: TptpFile): Either[CannotHandleInput, Seq[AnnotatedFormula]] = boundary {
    val formulas = tptpFile.inputs.map {
      case i: IncludeDirective =>
        break(Left(CannotHandleInput("cannot handle include directives", i)))
      case a: AnnotatedFormula => a
    }
    Right(formulas)
  }

  // ensures there are no steps with duplicate labels
  private def intoUniqueMap(steps: Seq[AnnotatedFormula]): Either[DifferentFormulasWithSameName, Map[String, AnnotatedFormula]] = boundary {
    val map = steps.foldLeft(Map.empty[String, AnnotatedFormula]) { (map, step) =>
      map.updatedWith(step.name) {
        case Some(formula) if step != formula =>
          break(Left(DifferentFormulasWithSameName(
            s"""formula $formula with name ${formula.name} is already present.
               |Attempted to add another formula $step with the same name.""".stripMargin
          )))
        case _ => Some(step)
      }
    }

    Right(map)
  }

  // ensures the map doesn't have any cycles with respect to the parent relation
  private def intoDag(map: Map[String, AnnotatedFormula]): Either[InferenceCycle, TptpDerivation] = {
    if isCyclic(map.keySet, n => map(n).parentLabels.toSet) then
      Left(InferenceCycle(s"Cycle detected in proof starting from node ${map.keySet.head}"))
    else Right(new TptpDerivation(map.toMap))
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
  val visited = scala.collection.mutable.Set[T]()
  def isPartOfCycle(node: T, path: Seq[T] = Seq.empty): Boolean = {
    if path.contains(node) then return true
    if visited.contains(node) then return false
    visited.add(node)
    successors(node).exists(p => isPartOfCycle(p, path :+ node))
  }

  nodes.exists(n => isPartOfCycle(n))
}

/**
* Represents a TptpDerivation with a designated root label which defines the
* end derived formula. This could be a $false formula which would make
* it a refutation, but coucld also be another formula. This allows picking
* any subderivation as a derivation.
*/
case class RootedTptpDerivation private (
    private val steps: Map[String, TptpDerivationStep],
    private val rootLabel: String
) {
  def usedDerivationSteps: Iterable[TptpDerivationStep] = steps.values
  def get(name: String): Option[TptpDerivationStep] = steps.get(name)
  def root: TptpDerivationStep = steps(rootLabel)
}

object RootedTptpDerivation {
  def fromDerivationAndRootLabel(derivation: TptpDerivation, rootLabel: String): Either[TptpDerivationImportError, RootedTptpDerivation] = boundary {
    val _ = derivation.get(rootLabel).getOrElse {
      break(Left(UnexpectedInput("end derivation label does not exist in proof")))
    }

    val usedAnnotatedFormulas = derivation.subDerivationRootedAt(rootLabel)
    val usedSteps = usedAnnotatedFormulas.map { a => a.name -> parseStep(a).getOrBreak }.toMap

    val usedNegatedConjectures = usedSteps.values.collect { case s: TptpNegatedConjectureStep => s }
    usedNegatedConjectures.find(s => !s.hasUnambiguousStatusAmong(Set("cth"))).map { s =>
      break(Left(StepWithInvalidStatus(s"there is a negated conjecture with an ambiguous status. should be cth", s)))
    }
    if usedNegatedConjectures.exists(c => derivation.hasNonConjectureParent(c.name)) then {
      break(Left(NegatedConjectureStepWithNonConjectureParent("there is a negated conjecture with a non-conjecture parent")))
    }
    if usedNegatedConjectures.exists(c => derivation.parentsOf(c.name).isEmpty) then {
      break(Left(NegatedConjectureWithoutParent("there is a negated conjecture without a parent")))
    }

    if usedNegatedConjectures.size > 1 then
      break(Left(UnexpectedInput("get more than one negated conjecture")))

    val usedPlainInferences = usedSteps.values.collect { case a: TptpPlainInferenceStep => a }
    usedPlainInferences.find(c => !c.hasUnambiguousStatusAmong(Set("thm", "esa"))).map { s =>
      break(Left(StepWithInvalidStatus("there is a plain inference with an ambiguous status. should be either thm or esa", s)))
    }
    usedPlainInferences.find(s => derivation.hasConjectureParent(s.name)).map { s =>
      break(Left(PlainInferenceWithConjectureParent("there is a plain inference with a conjecture parent", s)))
    }

    Right(RootedTptpDerivation(usedSteps, rootLabel))
  }

  def fromInputFileRefutation(file: InputFile): Either[TptpDerivationImportError, RootedTptpDerivation] = boundary {
    val derivation = TptpDerivation.fromInputFile(file).getOrBreak
    val refutationStep = derivation.annotatedFormulas.filter(_.formula == Bottom()).singleOption.getOrElse {
      break(Left(NoRefutationFound("no unique $false formula found in derivation")))
    }
    RootedTptpDerivation.fromDerivationAndRootLabel(derivation, refutationStep.name)
  }

  def fromInputFileAndRootLabel(file: InputFile, rootLabel: String): Either[TptpDerivationImportError, RootedTptpDerivation] = boundary {
    val tptpProofDag = TptpDerivation.fromInputFile(file).getOrBreak
    fromDerivationAndRootLabel(tptpProofDag, rootLabel)
  }

  private def parseStep(annotatedFormula: AnnotatedFormula): Either[TptpDerivationImportError, TptpDerivationStep] = boundary {
    val AnnotatedFormula(language, name, role, formula, annotations) = annotatedFormula
    language match {
      case "fof" | "cnf" => // we only support these languages for now
      case language      => break(Left(UnexpectedInput(s"unsupported input language $language. used in input $annotatedFormula")))
    }
    role match {
      case "axiom"              => parseAxiomStep(name, formula, annotations)
      case "conjecture"         => parseConjectureStep(name, formula, annotations)
      case "negated_conjecture" => parseNegatedConjectureStep(name, formula, annotations)
      case "plain"              => parsePlainInferenceStep(name, formula, annotations)
      case r                    => break(Left(UnexpectedInput(s"unsupported input role $r. used in input $annotatedFormula")))
    }
  }

  private def parseFOLFormula(formula: Formula): Either[TptpDerivationImportError, FOLFormula] = {
    if !(formula.isInstanceOf[FOLFormula]) then
      Left(UnexpectedInput(s"expected FOL formula, got ${formula.getClass}"))
    else
      Right(formula.asInstanceOf[FOLFormula])
  }

  private def parseAxiomStep(
      name: String,
      formula: Formula,
      annotations: Option[Annotations]
  ): Either[TptpDerivationImportError, TptpAxiomStep] = boundary {
    val fol = parseFOLFormula(formula).getOrBreak
    Right(TptpAxiomStep(name, fol, annotations))
  }

  private def parseConjectureStep(
      name: String,
      formula: Formula,
      annotations: Option[Annotations]
  ): Either[TptpDerivationImportError, TptpConjectureStep] = boundary {
    val fol = parseFOLFormula(formula).getOrBreak
    Right(TptpConjectureStep(name, fol, annotations))
  }

  private def parseNegatedConjectureStep(
      name: String,
      formula: Formula,
      annotations: Option[Annotations]
  ): Either[TptpDerivationImportError, TptpNegatedConjectureStep] = boundary { l ?=>
    val folFormula = parseFOLFormula(formula).getOrBreak(using l)
    val ann = annotations.getOrElse { break(Left(UnexpectedInput("got negated conjecture without source"))) }
    ann.source.parentLabels match {
      case Seq()           => break(Left(NegatedConjectureWithoutParent("got negated conjecture without parents")))
      case Seq(parent)     => Right(TptpNegatedConjectureStep(name, folFormula, parent, ann))
      case Seq(parent, _*) => break(Left(UnexpectedInput("got negated conjecture with multiple parents")))
    }
  }

  private def parsePlainInferenceStep(
      name: String,
      formula: Formula,
      annotationsOption: Option[Annotations]
  ): Either[TptpDerivationImportError, TptpSkolemizationStep | TptpPlainInferenceStep] = boundary {
    val folFormula = parseFOLFormula(formula).getOrBreak
    val annotations = annotationsOption.getOrElse { break(Left(UnexpectedInput("got plain inference without source"))) }
    val inference = annotations.source.asInferenceOption.getOrElse { break(Left(UnexpectedInput("got plain inference without inference record"))) }
    val optionalInfo = annotations.optionalInfo
    inference.rule match {
      case "skolemize" => parseSkolemizationStep(name, folFormula, inference, optionalInfo)
      case _ =>
        Right(TptpPlainInferenceStep(
          name,
          folFormula,
          annotations.source.parentLabels,
          annotations
        ))
    }
  }

  private def parseSkolemizationStep(
      name: String,
      formula: FOLFormula,
      inference: Source.Inference,
      optionalInfo: Seq[GeneralTerm]
  ): Either[TptpDerivationImportError, TptpSkolemizationStep] = boundary {
    val parent = inference.parentLabels match {
      case Seq()         => break(Left(UnexpectedInput("expected at least one parent label")))
      case Seq(_, _, _*) => break(Left(UnexpectedInput("expected at most one parent label")))
      case Seq(label)    => label
    }
    val newSkolemSymbols = inference.usefulInfo.collect {
      case TptpTerm("new_symbols", TptpTerm("skolem"), GeneralList(term)) => term.asInstanceOf[FOLConst]
      case TptpTerm("new_symbols", TptpTerm("skolem"), GeneralList(_, _)) =>
        break(Left(CannotHandleInput("cannot handle multiple skolemizations in one step yet", name)))
    }
    val newSkolemSymbol = newSkolemSymbols match {
      case Seq()         => break(Left(UnexpectedInput("expected at least one new_symbols(skolem,_) term")))
      case Seq(_, _, _*) => break(Left(UnexpectedInput("expected at most one new_symbols(skolem,_) term")))
      case Seq(term)     => term.asInstanceOf[FOLConst]
    }
    val boundVariableSkolemTermPairs = inference.usefulInfo.collect {
      case TptpTerm("skolemize", boundVariable, skolemTerm: FOLTerm) => (boundVariable.asInstanceOf[FOLVar], skolemTerm)
    }
    val (boundVariable, skolemTerm) = boundVariableSkolemTermPairs match {
      case Seq()         => break(Left(UnexpectedInput("expected at least one skolemize(_,_) term")))
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
      break(Left(SkolemizationStepWithDifferingSkolemTerms(s"expected skolem term to be $newSkolemSymbol, got $skolemFunctionConst", name)))
    }
    Right(TptpSkolemizationStep(
      name,
      formula,
      parent,
      skolemFunctionConst,
      contextVariables,
      boundVariable,
      Annotations(inference, optionalInfo)
    ))
  }

  extension (derivation: TptpDerivation) {
    def hasNonConjectureParent(formulaName: String): Boolean = {
      derivation.parentsOf(formulaName).exists(p => p.role != "conjecture")
    }

    def hasConjectureParent(formulaName: String): Boolean = {
      derivation.parentsOf(formulaName).exists(p => p.role == "conjecture")
    }
  }
}

/**
 * Represents a malformed input file e.g. one that contains an unknown parent step
 */
class MalformedInputFileException(s: String) extends IllegalArgumentException(s)

object TptpProofParser {
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
    case Source.General(term)                             => throw IllegalArgumentException(s"parent must be a simple term. got: $term")
  }
}

extension (annotatedFormula: AnnotatedFormula) {
  def parentLabels: Seq[String] = boundary {
    val annotations = annotatedFormula.annotations.getOrElse { break(Seq.empty) }
    annotations.source.parentLabels
  }
}

extension (annotations: Option[Annotations]) {
  def hasUnambiguousStatusAmong(statuses: Set[String]): Boolean = boundary {
    val ann = annotations.getOrElse { break(false) }
    val inferenceSource = ann.source.asInferenceOption.getOrElse { break(false) }
    val inferenceStatus = inferenceSource.statuses.singleOption.getOrElse { break(false) }

    statuses.contains(inferenceStatus)
  }
}

extension (step: TptpDerivationStep) {
  def annotationsOption: Option[Annotations] = step match {
    case TptpConjectureStep(_, _, annotationsOption) =>
      annotationsOption
    case TptpAxiomStep(_, _, annotationsOption) =>
      annotationsOption
    case TptpPlainInferenceStep(_, _, _, annotations) =>
      Some(annotations)
    case TptpNegatedConjectureStep(_, _, _, annotations) =>
      Some(annotations)
    case TptpSkolemizationStep(_, _, _, _, _, _, annotations) =>
      Some(annotations)
  }
  def hasUnambiguousStatusAmong(statuses: Set[String]): Boolean = boundary {
    step.annotationsOption.hasUnambiguousStatusAmong(statuses)
  }
}
