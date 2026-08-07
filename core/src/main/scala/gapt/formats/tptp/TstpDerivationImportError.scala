package gapt.formats.tptp

import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.Const

sealed trait TstpDerivationImportError {
  def message: String
}
case class InputSyntaxError(
    cause: IllegalArgumentException
) extends TstpDerivationImportError {
  override def message: String = cause.getMessage
}
case class DistinctFormulasWithSameName(
    label: String
) extends TstpDerivationImportError {
  override def message: String = s"there are multiple distinct formulas with the same name: $label"
}
case class InferenceCycle() extends TstpDerivationImportError {
  def message: String = "inference cycle detected"
}

case class StepWithInvalidStatus(
    stepName: String,
    actualStatuses: Iterable[String],
    validStatuses: Iterable[String]
) extends TstpDerivationImportError {
  override def message: String = s"$stepName has invalid statuses ${actualStatuses.mkString(", ")}. Expected one of ${validStatuses.mkString(", ")}"
}
case class StepWithInvalidInferenceRule(
    stepName: String,
    actualInferenceName: String,
    expectedInferenceName: String
) extends TstpDerivationImportError {
  override def message: String = s"$stepName has invalid inference name '$actualInferenceName'. Expected '$expectedInferenceName'"
}
case class NegatedConjectureStepWithNonConjectureParent(
    stepName: String
) extends TstpDerivationImportError {
  def message: String = s"step with name $stepName has a non-conjecture parent"
}
case class NegatedConjectureWithoutParent(
    stepName: String
) extends TstpDerivationImportError {
  def message: String = s"negated conjecture step with name $stepName has no parent"
}
case class NegatedConjectureWithMultipleDistinctParents() extends TstpDerivationImportError {
  def message: String = "got negated conjecture with multiple distinct parents"
}
case class PlainInferenceWithConjectureParent(
    step: TstpPlainInferenceStep
) extends TstpDerivationImportError {
  def message: String = s"plain inference step with name ${step.name} has a conjecture parent"
}
case class PlainInferenceWithoutSource(
    stepName: String
) extends TstpDerivationImportError {
  def message: String = s"plain inference step with name $stepName has no source"
}
case class IncorrectInference(
    stepName: String
) extends TstpDerivationImportError {
  def message: String = s"inference step with name $stepName is incorrect"
}
case class IncorrectSkolemization(
    reason: IncorrectSkolemizationReason
) extends TstpDerivationImportError {
  def message: String = reason.message
}
case class NonConstantSkolemTerm(
    stepName: String,
    term: FOLVar
) extends TstpDerivationImportError {
  def message: String = s"step $stepName: skolem term $term is not a constant, but a variable"
}
case class SkolemizationStepWithoutParent(
    stepName: String
) extends TstpDerivationImportError {
  def message: String = s"skolemization inference with name $stepName has no parent"
}
case class SkolemizationStepWithMultipleParents(
    stepName: String,
    parents: Seq[String]
) extends TstpDerivationImportError {
  def message: String = s"skolemization inference with name $stepName has multiple parents ${parents.mkString(", ")}"
}

case class NonExistentStep(
    stepName: String
) extends TstpDerivationImportError {
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
) extends TstpDerivationImportError {
  def message: String = s"skolemization step with name $stepName has differing skolem terms"
}
case class SkolemizationStepWithoutNewSymbols(
    stepName: String
) extends TstpDerivationImportError {
  def message: String = s"skolemization step with name $stepName has no new symbols"
}
case class SkolemizationStepWithoutBinding(
    stepName: String
) extends TstpDerivationImportError {
  def message: String = s"skolemization step with name $stepName has no skolemize(_,_) binding"
}
case class CannotHandleIncludeDirectives() extends TstpDerivationImportError {
  def message: String = "cannot handle include directives"
}
case class CannotHandleInput(stepName: String, reason: String) extends TstpDerivationImportError {
  def message: String = s"cannot handle input step with name $stepName: $reason"
}
case class NoRefutationFound() extends TstpDerivationImportError {
  def message: String = "no refutation found as there is no unique $false formula in the derivation"
}
case class NoConjectureFound() extends TstpDerivationImportError {
  def message: String = s"no conjecture found: $message"
}
case class UnexpectedInput(message: String) extends TstpDerivationImportError

case class NoStrongQuantifierFittingSkolemization(stepName: String, inputFormula: FOLFormula, skolemizedFormula: FOLFormula, skVar: FOLVar, skTerm: FOLTerm)
    extends IncorrectSkolemizationReason {
  def message: String = s"could not find a strong quantifier s.t. replacing $skVar with $skTerm transforms $inputFormula into $skolemizedFormula!"
}

case class MultipleStrongQuantifiersFittingSkolemization(stepName: String, inputFormula: FOLFormula, skolemizedFormula: FOLFormula, skVar: FOLVar, skTerm: FOLTerm)
    extends IncorrectSkolemizationReason {
  def message: String = s"could find multiple (non-unique) strong quantifiers s.t. replacing $skVar with $skTerm transforms $inputFormula into $skolemizedFormula!"
}
