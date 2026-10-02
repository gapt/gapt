package gapt.formats.tptp.check

import gapt.expr.formula.Formula
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLFunction
import gapt.expr.formula.fol.FOLFunctionConst
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLVar
import gapt.formats.InputFile
import gapt.formats.tptp.*
import gapt.utils.getOrBreak

import scala.util.boundary
import scala.util.boundary.break

sealed trait ParsedTstpDerivationStep {
  def name: String
  def role: String
  def formula: FOLFormula
  def parents: Seq[String]
}

trait FileSourceStep {
  def problemFile: String
  def problemFileLabel: String
}

case class ParsedTstpConjectureStep(
    name: String,
    formula: FOLFormula,
    problemFile: String,
    problemFileLabel: String
) extends ParsedTstpDerivationStep with FileSourceStep {
  def parents: Seq[String] = Seq.empty
  def role: String = "conjecture"
}

case class ParsedTstpAxiomStep(
    name: String,
    formula: FOLFormula,
    problemFile: String,
    problemFileLabel: String
) extends ParsedTstpDerivationStep with FileSourceStep {
  def parents: Seq[String] = Seq.empty
  def role: String = "axiom"
}

case class ParsedTstpPlainInferenceStep(
    name: String,
    formula: FOLFormula,
    parents: Seq[String],
    annotations: Annotations,
    source: Source.Inference
) extends ParsedTstpDerivationStep {
  def role: String = "plain"
}

case class ParsedTstpNegatedConjectureStep(
    name: String,
    formula: FOLFormula,
    parent: String,
    annotations: Annotations,
    source: Source.Inference
) extends ParsedTstpDerivationStep {
  def role: String = "negated_conjecture"
  def parents: Seq[String] = Seq(parent)
}

case class ParsedTstpSkolemizationStep(
    name: String,
    formula: FOLFormula,
    parent: String,
    source: Source.Inference,
    newSkolemSymbol: FOLFunctionConst,
    contextVariables: Seq[FOLVar],
    skolemizedSymbol: FOLVar,
    annotations: Annotations
) extends ParsedTstpDerivationStep {
  def parents: Seq[String] = Seq(parent)
  def role: String = "plain"
}

case class ParsedTstpDerivation(steps: Seq[ParsedTstpDerivationStep])

object ParsedTstpDerivation {

  def fromInputFile(input: InputFile): Either[TstpDerivationError, ParsedTstpDerivation] = {
    for
      tptp <- loadAsTptpFile(input)
      derivation <- parseTptpFile(tptp)
    yield derivation
  }

  private[check] def parseTptpFile(tptpFile: TptpFile): Either[TstpDerivationError, ParsedTstpDerivation] =
    for
      formulas <- intoAnnotatedFormulas(tptpFile)
      steps <- parseSteps(formulas)
    yield ParsedTstpDerivation(steps)

  private def loadAsTptpFile(input: InputFile): Either[InputSyntaxError, TptpFile] = {
    try Right(TptpImporter.loadWithoutIncludes(input))
    catch
      case e: IllegalArgumentException => Left(InputSyntaxError(e))
  }

  private def intoAnnotatedFormulas(
      tptpFile: TptpFile
  ): Either[CannotHandleIncludeDirectives, Seq[AnnotatedFormula]] = boundary {
    Right(tptpFile.inputs.map {
      case _: IncludeDirective       => break(Left(CannotHandleIncludeDirectives()))
      case formula: AnnotatedFormula => formula
    })
  }

  private def parseSteps(
      formulas: Seq[AnnotatedFormula]
  ): Either[TstpDerivationError, Seq[ParsedTstpDerivationStep]] = boundary {
    Right(formulas.map(parseStep(_).getOrBreak))
  }

  private def parseStep(annotatedFormula: AnnotatedFormula): Either[TstpDerivationError, ParsedTstpDerivationStep] = boundary {
    val AnnotatedFormula(language, name, role, formula, annotations) = annotatedFormula
    language match {
      case "fof" | "cnf" =>
      case language =>
        break(Left(UnexpectedInput(s"unsupported input language $language. used in input $annotatedFormula")))
    }
    role match {
      case "axiom" | "hypothesis" => parseAxiomStep(name, formula, annotations)
      case "conjecture"           => parseConjectureStep(name, formula, annotations)
      case "negated_conjecture"   => parseNegatedConjectureStep(name, formula, annotations)
      case "plain"                => parsePlainInferenceStep(name, formula, annotations)
      case role =>
        break(Left(UnexpectedInput(s"unsupported input role $role. used in input $annotatedFormula")))
    }
  }

  private def parseFOLFormula(formula: Formula): Either[TstpDerivationError, FOLFormula] = {
    if formula.isInstanceOf[FOLFormula] then Right(formula.asInstanceOf[FOLFormula])
    else Left(UnexpectedInput(s"expected FOL formula, got ${formula.getClass}"))
  }

  private def parseAxiomStep(
      name: String,
      formula: Formula,
      annotations: Option[Annotations]
  ): Either[TstpDerivationError, ParsedTstpAxiomStep] = boundary {
    val fol = parseFOLFormula(formula).getOrBreak
    val (fileName, label) = parseFileDirective(name, annotations).getOrBreak
    Right(ParsedTstpAxiomStep(name, fol, fileName, label))
  }

  private def parseConjectureStep(
      name: String,
      formula: Formula,
      annotations: Option[Annotations]
  ): Either[TstpDerivationError, ParsedTstpConjectureStep] = boundary {
    val fol = parseFOLFormula(formula).getOrBreak
    val (fileName, label) = parseFileDirective(name, annotations).getOrBreak
    Right(ParsedTstpConjectureStep(name, fol, fileName, label))
  }

  private def parseFileDirective(
      stepName: String,
      annotationsOption: Option[Annotations]
  ): Either[TstpDerivationError, (fileName: String, label: String)] = boundary {
    val annotations = annotationsOption.getOrElse {
      break(Left(SourceMissing(stepName)))
    }
    annotations.source match {
      case Source.File(fileName, Some(label)) => Right((fileName, label))
      case Source.File(_, None)               => break(Left(FileDirectiveLabelMissing(stepName)))
      case _                                  => break(Left(FileDirectiveMissing(stepName)))
    }
  }

  private def parseNegatedConjectureStep(
      name: String,
      formula: Formula,
      annotationsOption: Option[Annotations]
  ): Either[TstpDerivationError, ParsedTstpNegatedConjectureStep] = boundary {
    val folFormula = parseFOLFormula(formula).getOrBreak
    val annotations = annotationsOption.getOrElse {
      break(Left(UnexpectedInput("got negated conjecture without source")))
    }
    val inference = annotations.source match {
      case inference: Source.Inference => inference
      case _                           => break(Left(UnexpectedInput(s"got negated conjecture inference without inference record: $name")))
    }
    val expectedRule = "negated_conjecture"
    if inference.rule != expectedRule then
      break(Left(StepWithInvalidInferenceRule(name, inference.rule, expectedRule)))

    inference.parentLabels.distinct match {
      case Seq()       => break(Left(NegatedConjectureWithoutParent(name)))
      case Seq(parent) => Right(ParsedTstpNegatedConjectureStep(name, folFormula, parent, annotations, inference))
      case Seq(_, _*)  => break(Left(NegatedConjectureWithMultipleDistinctParents()))
    }
  }

  private def parsePlainInferenceStep(
      name: String,
      formula: Formula,
      annotationsOption: Option[Annotations]
  ): Either[TstpDerivationError, ParsedTstpSkolemizationStep | ParsedTstpPlainInferenceStep] = boundary {
    val folFormula = parseFOLFormula(formula).getOrBreak
    val annotations = annotationsOption.getOrElse {
      break(Left(PlainInferenceWithoutSource(name)))
    }
    val inference = annotations.source match {
      case inference: Source.Inference => inference
      case _: Source.Internal          => break(Left(CannotHandleInput(name, "cannot handle internal sources")))
      case _                           => break(Left(PlainInferenceWithoutSource(name)))
    }

    inference.rule match {
      case "skolemize" => parseSkolemizationStep(name, folFormula, inference, annotations.optionalInfo)
      case _ =>
        Right(ParsedTstpPlainInferenceStep(name, folFormula, inference.parentLabels, annotations, inference))
    }
  }

  private def parseSkolemizationStep(
      name: String,
      formula: FOLFormula,
      inference: Source.Inference,
      optionalInfo: Seq[GeneralTerm]
  ): Either[TstpDerivationError, ParsedTstpSkolemizationStep] = boundary {
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
      case TptpTerm("skolemize", boundVariable: FOLVar, skolemTerm: FOLTerm) => (boundVariable, skolemTerm)
      case TptpTerm("skolemize", _*) =>
        break(Left(UnexpectedInput("expected skolemize(X,t) term where X is a variable and t is a term")))
    }
    val (boundVariable, skolemTerm) = boundVariableSkolemTermPairs match {
      case Seq()         => break(Left(SkolemizationStepWithoutBinding(name)))
      case Seq(_, _, _*) => break(Left(UnexpectedInput("expected at most one skolemize(_,_) term")))
      case Seq(pair)     => pair
    }
    val (skolemFunctionConst, args) = skolemTerm match {
      case FOLFunction(head, args) => (FOLFunctionConst(head, args.size), args)
      case _                       => break(Left(UnexpectedInput("expected skolem term to be a FOL term")))
    }
    val contextVariables = args.map {
      case variable: FOLVar => variable
      case _                => break(Left(UnexpectedInput("expected skolem term arguments to be first-order variables")))
    }
    if newSkolemSymbol.name != skolemFunctionConst.name then
      break(Left(SkolemizationStepWithNewSymbolDifferingFromSkolemizeTerm(name)))

    Right(ParsedTstpSkolemizationStep(
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
}
