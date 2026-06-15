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
import gapt.formats.tptp.check.TptpProofDag

sealed trait TptpProofStep {
  def name: String
  def formula: Formula
}

enum InferenceStatus {
  case Thm
  case Cth
  case Esa
}

sealed trait TptpInference extends TptpProofStep {
  def status: InferenceStatus
  def parents: Seq[String]
}

case class TptpAxiomStep(
    val name: String,
    val formula: Formula
) extends TptpProofStep
case class TptpConjectureStep(
    val name: String,
    val formula: Formula
) extends TptpProofStep
case class TptpNegatedConjectureStep(
    val name: String,
    val formula: Formula,
    val status: InferenceStatus,
    val conjectureStep: TptpConjectureStep
) extends TptpInference {
  def parents: Seq[String] = Seq(conjectureStep.name)
}
case class TptpPlainInfenreceStep(
    val name: String,
    val formula: Formula,
    val status: InferenceStatus,
    val premises: Seq[TptpProofStep]
) extends TptpInference {
  def parents: Seq[String] = premises.map(_.name)
}
case class TptpPlainSkolemizationInferenceStep(
    val name: String,
    val formula: Formula,
    val status: InferenceStatus,
    val skolemSymbol: Const,
    val boundVariable: Var,
    val skolemParameters: Seq[Var],
    val premise: TptpProofStep
) extends TptpInference {
  def parents: Seq[String] = Seq.empty
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

extension (formula: AnnotatedFormula) {
  def asConjectureStep: Option[TptpConjectureStep] = {
    formula.role match {
      case "conjecture" => Some(TptpConjectureStep(formula.name, formula.formula))
      case _            => None
    }
  }

  def isConjectureStep: Boolean = asConjectureStep.isDefined

  def claimsIsNegatedConjectureStep: Boolean = formula.role == "negated_conjecture"

  def inferenceRecord: Option[Source.Inference] = formula.annotations match {
    case Some(Annotations(Source.Inference(rule, usefulInfo, parents), _)) =>
      Some(Source.Inference(rule, usefulInfo, parents))
    case _ => None
  }
}

extension (using tptpFile: TptpFile)(a: AnnotatedFormula) {
  // assumes that parents of a actually occur in tptpFile
  def parents: Seq[AnnotatedFormula] = {
    val inferenceRecord = a.inferenceRecord match {
      case None    => return Seq.empty
      case Some(i) => i
    }
    inferenceRecord.parents.map(p =>
      tptpFile.inputs.collect {
        case af @ AnnotatedFormula(_, name, _, _, _) if Source.Name(name) == p.source => af
      }.single
    )
  }
  def ancestors: Seq[AnnotatedFormula] = {
    // TODO: catch cycles
    a.parents ++ a.parents.flatMap(_.ancestors)
  }
  def isUsedInDerivationOf(b: AnnotatedFormula): Boolean = {
    a == b || a.ancestors.contains(b)
  }
  def isConjectureOf(b: AnnotatedFormula): Boolean = {
    // a.isConjectureStep
    // && b.claimsIsNegatedConjectureStep
    b.parents.contains(a)
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

object TptpProofParser {
  def parseTptpRefutationSketch(dag: TptpProofDag): TptpRefutationSketch = {
    given tptpFile: TptpFile = TptpFile(dag.map(_._2).toSeq)
    val input = InputFile.fromString(tptpFile.toString)
    val (_, sketch) = parse(input)
    val refutationHead = tptpFile.inputs.collect {
      case a @ AnnotatedFormula(_, _, _, Bottom(), _) => a
    }.single
    val usedNegatedConjectures = dag.values.collect {
      case a @ AnnotatedFormula(_, _, "negated_conjecture", _, _)
          if dag.isUsedInDerivationOf(a.name, refutationHead.name) => a
    }

    if usedNegatedConjectures.isEmpty then
      return TptpRefutationSketch(sketch, None)

    if usedNegatedConjectures.size > 1 then
      throw new IllegalArgumentException(s"Expected exactly one negated conjecture used in the refutation sketch, got ${usedNegatedConjectures.size}")

    val negatedConjecture = usedNegatedConjectures.head
    val conjectures = tptpFile.inputs.collect {
      case a @ AnnotatedFormula(_, _, "conjecture", _, _) => a
    }
    val conjecture = conjectures.head
    TptpRefutationSketch(sketch, Some((conjecture.formula, negatedConjecture.formula)))
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
        case f @ AnnotatedFormula(_, _, _, _, Some(Annotations(source, _))) if getParents(source).toSet.intersect(stepsWithStrongQuants).isEmpty => f
        case AnnotatedFormula(_, label, "conjecture", formula, _) =>
          AnnotatedFormula("fof", label, "conjecture", formula, None)
        case f => AnnotatedFormula("fof", f.name, "axiom", f.formula, None)
      })
  }

  def parse(tptp: TptpFile, ignoreStrongQuants: Boolean): (Sequent[FOLFormula], RefutationSketch) = {
    var tptpFile = tptp
    if (ignoreStrongQuants) tptpFile = removeStrongQuants(tptpFile)
    val (endSequent, labelledCNF) = extractEndSequentAndCNF(tptpFile)
    endSequent -> parseSteps(tptpFile, labelledCNF)
  }

  def parse(out: InputFile, ignoreStrongQuants: Boolean = false): (Sequent[FOLFormula], RefutationSketch) = {
    val tptpFile = TptpImporter.loadWithoutIncludes(out)
    parse(tptpFile, ignoreStrongQuants)
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

  def getParents(source: Source): Seq[String] = source match {
    case Source.Name(name)               => Seq(name)
    case Source.Inference(_, _, parents) => parents.flatMap(p => getParents(p.source))
    case Source.Internal(_, _, parents)  => parents.flatMap(p => getParents(p.source))
    case Source.File(_, _)               => Seq.empty // for now we treat file sources as axioms that don't have parents
    case Source.Theory(_, _)             => Seq.empty
    case Source.Creator(_, _, parents)   => parents.flatMap(p => getParents(p.source))
    case Source.Unknown                  => Seq.empty
    case Source.List(sources)            => sources.flatMap(s => getParents(s))
    case Source.General(s) => s match {
        case GeneralColon(TptpTerm(label), _) => Seq(label)
        case TptpTerm(dagSource)              => Seq(dagSource)
      }
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
        val sketchParents = getParents(source).flatMap(convert)
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
        val Seq(splittedClause, _*) = getParents(source).flatMap(convert): @unchecked

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
        Seq(SketchSplitCombine(getParents(source).flatMap(convert)))
      }

      def convertRemainingCases(conclusion: FOLFormula, source: Source): Seq[RefutationSketch] = {
        CNFp(conclusion).toSeq match {
          case Seq(conclusionClause) =>
            val sketchParents = getParents(source).flatMap(convert)
            val conclusionClause_ = filterVampireSplits(conclusionClause)
            val sketchParents_ = sketchParents.find(p => clauseSubsumption(p.conclusion, conclusionClause_).isDefined).fold(sketchParents)(Seq(_))
            Seq(SketchInference(conclusionClause_, sketchParents_))
          case clauses => getParents(source).flatMap(convert)
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
              if labelledCNF.contains(label) =>
            CNFp(axiom).toSeq match {
              case Seq(axiomClause) =>
                Seq(SketchInference(
                  axiomClause,
                  labelledCNF(label).map(SketchAxiom.apply)
                ))
              case clauses => labelledCNF(label).map(SketchAxiom.apply)
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
