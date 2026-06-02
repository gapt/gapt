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
}

object TptpProofParser {
  def parseTptpRefutationSketch(input: InputFile): TptpRefutationSketch = {
    val (_, sketch) = parse(input)
    given tptpFile: TptpFile = TptpImporter.loadWithoutIncludes(input)
    val refutationHead = tptpFile.inputs.collect {
      case a @ AnnotatedFormula(_, _, _, Bottom(), _) => a
    }.single
    val usedNegatedConjectures = tptpFile.inputs.collect {
      case a @ AnnotatedFormula(_, _, "negated_conjecture", _, _) if a.isUsedInDerivationOf(refutationHead) => a
    }

    if usedNegatedConjectures.isEmpty then
      return TptpRefutationSketch(sketch, None)

    if usedNegatedConjectures.size > 1 then
      throw new IllegalArgumentException("Expected exactly one negated conjecture used in the refutation sketch, got " + usedNegatedConjectures.size)

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
    tptpFile = inventSources(tptpFile)
    val (endSequent, labelledCNF) = extractEndSequentAndCNF(tptpFile)
    endSequent -> parseSteps(tptpFile, labelledCNF)
  }

  def parse(out: InputFile, ignoreStrongQuants: Boolean = false): (Sequent[FOLFormula], RefutationSketch) = {
    val tptpFile = TptpImporter.loadWithoutIncludes(out)
    parse(tptpFile, ignoreStrongQuants)
  }

  def inventSources(stepList: TptpFile): TptpFile = TptpFile(stepList.inputs.map {
    case af @ AnnotatedFormula(_, label, role @ ("axiom" | "hypothesis" | "conjecture" | "negated_conjecture"), formula, None) =>
      af.copy(annotations = Some(Annotations(Source.File("unknown", Some(s"source_$label")), Seq.empty)))
    case af @ AnnotatedFormula(_, label, role @ ("axiom" | "hypothesis" | "conjecture" | "negated_conjecture"), formula, Some(Annotations(Source.File(_, Some("unknown")), _))) =>
      af.copy(annotations = Some(Annotations(Source.File("unknown", Some(s"source_$label")), Seq.empty)))
    case other => other
  })

  def extractEndSequentAndCNF(stepList: TptpFile): (Sequent[FOLFormula], Map[String, Seq[FOLClause]]) = {
    var endSequent = Sequent[FOLFormula]()
    val labelledCNF = mutable.Map[String, Seq[FOLClause]]().withDefaultValue(Seq())

    stepList.inputs.foreach {
      case AnnotatedFormula("fof", _, "conjecture", formula: FOLFormula, Some(Annotations(Source.File(_, Some(label)), _))) =>
        endSequent :+= formula
        labelledCNF(label) ++= CNFn(formula).toSeq
      case AnnotatedFormula(lang, _, _, formula: FOLFormula, Some(Annotations(Source.File(_, Some(label)), _))) =>
        endSequent +:= (if (lang == "cnf") universalClosure(formula) else formula)
        labelledCNF(label) ++= CNFp(formula).toSeq
      case _ =>
    }

    endSequent -> labelledCNF.toMap
  }

  def getParents(source: Source): Seq[String] = source match {
    case Source.Name(name)               => Seq(name)
    case Source.Inference(_, _, parents) => parents.flatMap(p => getParents(p.source))
    case Source.Internal(_, _, parents)  => parents.flatMap(p => getParents(p.source))
    case Source.File(_, _)               => Seq()
    case Source.General(s) => s match {
        case TptpTerm("theory", TptpTerm("equality", _*), _*) => Seq()
        case GeneralColon(TptpTerm(label), _)                 => Seq(label)
        case TptpTerm(dagSource)                              => Seq(dagSource)
      }
  }

  def getParents(justification: GeneralTerm): Seq[String] = getParents(Source.General(justification))

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
          case AnnotatedFormula("fof", _, "conjecture", _, Some(Annotations(Source.File(_, Some(label)), _))) =>
            labelledCNF(label).map(SketchAxiom.apply)
          case AnnotatedFormula(_, _, _, axiom: FOLFormula, Some(Annotations(Source.File(_, Some(label)), _))) =>
            CNFp(axiom).toSeq match {
              case Seq(axiomClause) =>
                Seq(SketchInference(
                  axiomClause,
                  labelledCNF(label).map(SketchAxiom.apply)
                ))
              case clauses => labelledCNF(label).map(SketchAxiom.apply)
            }
          case AnnotatedFormula("cnf", _, "axiom", axiom: FOLFormula, None) =>
            val label = stepName
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
