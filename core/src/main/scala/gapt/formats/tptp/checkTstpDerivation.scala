package gapt.formats.tptp.check

import gapt.expr.Abs
import gapt.expr.App
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.formula.*
import gapt.expr.formula.Formula
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLVar
import gapt.expr.ty.Ti
import gapt.expr.util.constants
import gapt.expr.util.freeVariables
import gapt.formats.tptp.*
import TstpCheckSyntax.*
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
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.ProofLink
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.provers.ResolutionProver
import gapt.provers.escargot.Escargot
import gapt.utils.getOrBreak

import java.nio.file.Paths
import java.util.concurrent.atomic.AtomicInteger
import scala.concurrent.Await
import scala.concurrent.ExecutionContext
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.concurrent.Promise
import scala.concurrent.duration.Duration
import scala.util.Failure
import scala.util.Success
import scala.util.boundary
import scala.util.control.NonFatal

import boundary.break
import scala.collection.SeqMap

sealed trait TstpDerivationError {
  def message: String
}
sealed trait VerifiedBadReason extends TstpDerivationError
sealed trait VerifiedUnknownReason extends TstpDerivationError

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

enum TstpStatus(val value: String) {
  case Thm extends TstpStatus("thm")
  case Cth extends TstpStatus("cth")
  case Esa extends TstpStatus("esa")
  case Other(override val value: String) extends TstpStatus(value)
}

object TstpStatus {
  def fromValue(value: String): TstpStatus = value match {
    case Thm.value => Thm
    case Cth.value => Cth
    case Esa.value => Esa
    case other     => Other(other)
  }
}

private sealed trait TstpReplayObligation {
  def step: ParsedTstpDerivationStep
  def sequents: Seq[Sequent[FOLFormula]]
}

private object TstpReplayObligation {
  final case class Axiom(step: ParsedTstpAxiomStep) extends TstpReplayObligation {
    def sequents: Seq[Sequent[FOLFormula]] = Seq.empty
  }
  final case class Conjecture(step: ParsedTstpConjectureStep) extends TstpReplayObligation {
    def sequents: Seq[Sequent[FOLFormula]] = Seq.empty
  }
  final case class Skolemization(step: ParsedTstpSkolemizationStep) extends TstpReplayObligation {
    def sequents: Seq[Sequent[FOLFormula]] = Seq.empty
  }
  final case class Entailment(step: ParsedTstpPlainInferenceStep, premises: Seq[FOLFormula]) extends TstpReplayObligation {
    def sequents: Seq[Sequent[FOLFormula]] = Seq(Sequent(premises, Vector(step.formula)))
  }

  final case class NegatedConjectureEquivalence(
      step: ParsedTstpNegatedConjectureStep,
      conjecture: FOLFormula
  ) extends TstpReplayObligation {
    val negatedConjectureToFormula: Sequent[FOLFormula] = Neg(conjecture) +: Sequent() :+ step.formula
    val formulaToNegatedConjecture: Sequent[FOLFormula] = step.formula +: Sequent() :+ Neg(conjecture)
    def sequents: Seq[Sequent[FOLFormula]] = Seq(negatedConjectureToFormula, formulaToNegatedConjecture)
  }

  def forStep(step: ParsedTstpDerivationStep, derivation: StructurallyCorrectTstpDerivation): TstpReplayObligation =
    step match {
      case axiom: ParsedTstpAxiomStep                 => Axiom(axiom)
      case conjecture: ParsedTstpConjectureStep       => Conjecture(conjecture)
      case skolemization: ParsedTstpSkolemizationStep => Skolemization(skolemization)
      case plain: ParsedTstpPlainInferenceStep =>
        Entailment(plain, plain.parents.map(p => derivation.get(p).get.formula))
      case negated: ParsedTstpNegatedConjectureStep =>
        NegatedConjectureEquivalence(negated, derivation.get(negated.parent).get.formula)
    }
}

private def replayTstpDerivation[A](
    derivation: VerifiedSkolemizationsTstpDerivation
)(handle: TstpReplayObligation => A): Unit =
  derivation.structurallyCorrect.stepsTopologicallyOrdered.foreach { step =>
    handle(TstpReplayObligation.forStep(step, derivation.structurallyCorrect))
  }

/**
* Attempts to replay the inferences in the given StructurallyCorrectTstpDerivation into a Context containing
* LKProofs for every inference step in the StructurallyCorrectTstpDerivation
*/
def buildTstpDerivationToProofContext(
    derivation: StructurallyCorrectTstpDerivation,
    prover: ResolutionProver = Escargot
): Either[IncorrectInference | IncorrectSkolemization, Context] =
  VerifiedSkolemizationsTstpDerivation.fromStructurallyCorrect(derivation).flatMap {
    buildTstpDerivationToProofContext(_, prover)
  }

def buildTstpDerivationToProofContext(
    derivation: VerifiedSkolemizationsTstpDerivation,
    prover: ResolutionProver
): Either[IncorrectInference, Context] = boundary { outer ?=>
  val ctx = buildTstpDerivationContext(derivation)
  given context: MutableContext = ctx.newMutable

  def addToContext(update: => Update) = {
    context += update
  }

  def replayProof(inferenceName: String, sequentToProve: Sequent[FOLFormula]): LKProof =
    val replayContext = context
    prover.getLKProof(sequentToProve)(using replayContext).getOrElse {
      break(Left(IncorrectInference(inferenceName, sequentToProve)))
    }

  case class VariableCapturingProofDeclaration(lhs: Expr, proof: LKProof) extends Update {
    def link = ProofLink(lhs, proof.endSequent)

    override def apply(ctx: Context): State =
      ctx + ProofNameDeclaration(lhs, proof.endSequent, freeVariables(proof.endSequent)) + ProofDefinitionDeclaration(lhs, proof) state

    override def toString: String =
      s"VariableCapturingProofDeclaration($lhs, ${proof.endSequent})"
  }

  def proofDeclaration(name: String, proof: LKProof): VariableCapturingProofDeclaration =
    VariableCapturingProofDeclaration(FOLConst(name), proof)

  def handleObligation(obligation: TstpReplayObligation): Unit = obligation match {
    case TstpReplayObligation.Conjecture(_) =>
    case TstpReplayObligation.Axiom(s) =>
      addToContext(proofDeclaration(s.name, LogicalAxiom(s.formula)))
    case TstpReplayObligation.Skolemization(s) =>
      val skolemizationStep = derivation.verifiedSkolemization(s.name).get
      addToContext(proofDeclaration(s.name, skolemizationStep.proof))
    case entailment: TstpReplayObligation.Entailment =>
      val proof = replayProof(entailment.step.name, entailment.sequents.head)
      addToContext(proofDeclaration(entailment.step.name, proof))
    case equivalence: TstpReplayObligation.NegatedConjectureEquivalence =>
      val s = equivalence.step
      // TSTP requires equivalence between the negated conjecture and this formula.
      val negatedConjectureToFormulaProof = replayProof(s.name, equivalence.negatedConjectureToFormula)
      val formulaToNegatedConjectureProof = replayProof(s.name, equivalence.formulaToNegatedConjecture)
      val iffProof = AndRightRule(
        ImpRightRule(negatedConjectureToFormulaProof, Ant(0), Suc(0)),
        Suc(0),
        ImpRightRule(formulaToNegatedConjectureProof, Ant(0), Suc(0)),
        Suc(0)
      )
      val weakenedProof = WeakeningLeftRule(negatedConjectureToFormulaProof, iffProof.conclusion.succedent.head)
      val cutProof = CutRule(iffProof, weakenedProof)
      addToContext(proofDeclaration(s.name, cutProof))
  }

  replayTstpDerivation(derivation)(handleObligation)

  Right(context.toImmutable)
}

/**
 * Combines a replayed TSTP proof with the proofs of its ancestors by adding cuts for the inference parents.
 *
 * The returned proof represents the proof structure inherent in the TSTP derivation, with cuts for its parent
 * inferences, but without filling in those inferences' replay proofs. Use [[instantiateLKProof]] to obtain the full
 * proof with the replay proofs instantiated. Proofs in the context are kept uncombined during replay to avoid
 * duplicating shared parent proofs; this method combines only the requested step's ancestors and memoizes shared
 * ancestors. Negated-conjecture steps are already represented by their own equivalence proof and have no proof
 * parent to combine.
 *
 * @param derivation The structurally correct TSTP derivation that records each step's parents.
 * @param proofContext The context containing the replayed proof definition for each inference step.
 * @param name The label of the step whose proof should be combined with its ancestors.
 * @return A proof with cuts connecting the requested step to its ancestor proofs.
 */
def combineTstpProofWithAncestors(
    derivation: StructurallyCorrectTstpDerivation,
    proofContext: Context,
    name: String
): LKProof = {
  val steps = derivation.stepsIterator.map(step => step.name -> step).toMap
  val combined = scala.collection.mutable.Map.empty[String, LKProof]
  def combine(label: String): LKProof = combined.getOrElseUpdate(
    label, {
      val step = steps(label)
      val proofLink = proofContext.get[ProofNames].link(FOLConst(label)).get
      val parents = step match {
        case _: ParsedTstpNegatedConjectureStep => Seq.empty
        case _                                  => step.parents
      }
      parents.foldLeft(proofLink: LKProof) { (currentProof, parent) =>
        CutRule(combine(parent), currentProof)
      }
    }
  )
  combine(name)
}

/** Instantiates the replay proofs into the TSTP proof structure for the requested step. */
def instantiateLKProof(
    derivation: StructurallyCorrectTstpDerivation,
    proofContext: Context,
    name: String
): LKProof =
  gapt.proofs.lk.util.instantiateProof(combineTstpProofWithAncestors(derivation, proofContext, name))(using proofContext)

/**
* Attempts to replay the inferences in the given StructurallyCorrectTstpDerivation, but does not create
* a context or LKProofs of the inferences for performance. Use this, if you are
* interested in whether the given derivation is correct or not, but do not care
* about the replayed proofs
*/
def checkDerivationHasNoIncorrectInferences(
    derivation: StructurallyCorrectTstpDerivation,
    prover: ResolutionProver = Escargot
): Either[IncorrectInference | IncorrectSkolemization, Unit] =
  VerifiedSkolemizationsTstpDerivation.fromStructurallyCorrect(derivation).flatMap {
    checkDerivationHasNoIncorrectInferences(_, prover)
  }

def checkDerivationHasNoIncorrectInferences(
    derivation: VerifiedSkolemizationsTstpDerivation,
    prover: ResolutionProver
): Either[IncorrectInference, Unit] = boundary {
  val ctx = buildTstpDerivationContext(derivation)
  val context: MutableContext = ctx.newMutable

  def isValid(inferenceName: String, sequentToProve: Sequent[FOLFormula]): Boolean = {
    val replayContext = context.newMutable
    prover.isValid(sequentToProve)(using replayContext)
  }

  val futures = scala.collection.mutable.ArrayBuffer.empty[Future[(ParsedTstpDerivationStep, Sequent[FOLFormula], Boolean)]]
  def checkObligation(obligation: TstpReplayObligation): Unit =
    obligation.sequents.foreach { sequent =>
      val step = obligation.step
      futures += Future { (step, sequent, isValid(step.name, sequent)) }
    }

  replayTstpDerivation(derivation) {
    case obligation: TstpReplayObligation.Entailment                   => checkObligation(obligation)
    case obligation: TstpReplayObligation.NegatedConjectureEquivalence => checkObligation(obligation)
    case _                                                             =>
  }
  val incorrectStep = firstCompletedMatching(futures)((_, _, isValid) => !isValid)
  val result = Await.result(incorrectStep, Duration.Inf)
  result match {
    case None                     => Right(())
    case Some((step, sequent, _)) => Left(IncorrectInference(step.name, sequent))
  }
}

private def firstCompletedMatching[A](futures: Iterable[Future[A]])(predicate: A => Boolean): Future[Option[A]] = {
  if futures.isEmpty then Future.successful(None)
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
            if predicate(value) then result.trySuccess(Some(value))
            else completedWithoutMatch()
          } catch {
            case NonFatal(error) => result.tryFailure(error)
          }
        case Failure(e) =>
          result.tryFailure(e)
      }
    }

    result.future
  }
}

private def buildTstpDerivationContext(
    derivation: VerifiedSkolemizationsTstpDerivation
): ImmutableContext = {
  val context: MutableContext = MutableContext.default()
  context += Sort(Ti)

  def addConstantToContextIfNotPresent(c: Const): Unit = {
    if context.constant(c.name).isEmpty
    then context += c
  }

  derivation.structurallyCorrect.stepsIterator.foreach { s =>
    constants.all(s.formula).foreach { c =>
      addConstantToContextIfNotPresent(c)
    }
  }

  derivation.verifiedSkolemizations.foreach { skolemization =>
    import gapt.proofs.context.facet.skolemFunsFacet
    addConstantToContextIfNotPresent(skolemization.skolemSymbol)
    context += { ctx => ctx.state.update[SkolemFunctions](_ + (skolemization.skolemSymbol, skolemization.skolemDefinition)) }
  }

  context.toImmutable
}

private[check] def renameConsts(renaming: PartialFunction[Const, String])(expr: Expr): Expr = expr match {
  case v: Var         => v
  case c: Const       => Const(renaming.applyOrElse(c, _ => c.name), c.ty, c.params)
  case App(head, arg) => App(renameConsts(renaming)(head), renameConsts(renaming)(arg))
  case Abs(v, body)   => Abs(v, renameConsts(renaming)(body))
}

trait FileNameResolver {
  def apply(fileName: String): Either[FileNotFound, String]
}

extension [R <: FileNameResolver](r: R) {
  def extend(f: FileNameResolver): FileNameResolver = fileName =>
    boundary { Right(f(fileName).getOrElse { r(fileName).getOrBreak }) }

  def relativeTo(root: os.Path): FileNameResolver = fileName =>
    if Paths.get(fileName).isAbsolute() then r(fileName)
    else r((root / os.RelPath(fileName)).toString)
}

object FileNameResolver {
  val empty: FileNameResolver = fileName => Left(FileNotFound(fileName))
  val absolute: FileNameResolver = fileName => {
    val path = os.Path(fileName, os.pwd)
    if os.exists(path) then Right(os.read(path))
    else Left(FileNotFound(fileName))
  }
  given FileNameResolver = absolute
}

/**
* Checks whether a given input file is a correct TSTP derivation according to the
* rules of the ProoVer competiton 2026. Returns the corresponding SZS status:
* - VerifiedGood: All proof steps are checked to be correct
* - VerifiedBad: There was a mistake in the proof
* - VerifiedUnknown: We could not determine whether the input is a correct proof or not
*
* @param file The input file to check.
* @param resolver The resolver to use for resolving file names.
* @return The [[SzsStatus]] of the check.
*/
def checkTstpDerivation(fileName: String)(using resolver: FileNameResolver): SzsStatus = {
  val result =
    try {
      for
        input <- resolver(fileName)
        derivation <- StructurallyCorrectTstpDerivation.fromInputFile(
          NamedTptpInputFile(fileName, input)
        )
        _ <- checkDerivationHasRefutation(derivation)
        _ <- checkDerivationHasCorrectFileDirectives(derivation, fileName)
        _ <- checkDerivationHasCorrectStatuses(derivation)
        verifiedDerivation <- VerifiedSkolemizationsTstpDerivation.fromStructurallyCorrect(derivation)
        _ <- checkDerivationHasNoIncorrectInferences(verifiedDerivation, Escargot)
      yield ()
    } catch {
      case e: OutOfMemoryError   => Left(UnexpectedException(e))
      case e: StackOverflowError => Left(UnexpectedException(e))
      case NonFatal(e)           => Left(UnexpectedException(e))
    }

  result match {
    case Left(reason: VerifiedUnknownReason) => SzsStatus.Unknown(reason)
    case Left(reason: VerifiedBadReason)     => SzsStatus.VerifiedBad(reason)
    case Right(_)                            => SzsStatus.VerifiedGood
  }
}

def checkDerivationHasRefutation(derivation: StructurallyCorrectTstpDerivation): Either[TstpDerivationError, Unit] = {
  if derivation.nonConjectureRootRefutationLabels.isEmpty then
    Left(NoRefutationFound())
  else
    Right(())
}

def checkDerivationHasCorrectStatuses(derivation: StructurallyCorrectTstpDerivation): Either[TstpDerivationError, Unit] = boundary {
  def invalidNestedSource(source: Source, isOuter: Boolean = false): Option[Source.Inference] = source match {
    case inference @ Source.Inference(_, _, parents) =>
      if !isOuter && inference.statuses.toSet != Set(TstpStatus.Thm) then Some(inference)
      else parents.iterator.map(parent => invalidNestedSource(parent.source)).collectFirst { case Some(nested) => nested }
    case Source.Internal(_, _, parents) =>
      parents.iterator.map(parent => invalidNestedSource(parent.source)).collectFirst { case Some(nested) => nested }
    case Source.Creator(_, _, parents) =>
      parents.iterator.map(parent => invalidNestedSource(parent.source)).collectFirst { case Some(nested) => nested }
    case Source.List(sources) =>
      sources.iterator.map(invalidNestedSource(_)).collectFirst { case Some(nested) => nested }
    case _ => None
  }

  def checkNestedStatuses(stepName: String, source: Source): Unit =
    invalidNestedSource(source, isOuter = true).foreach { inference =>
      break(Left(PlainInferenceWithNonThmNestedInference(stepName, inference)))
    }

  def firstNestedInference(source: Source): Option[Source.Inference] = source match {
    case Source.Inference(_, _, parents) => parents.iterator.flatMap(parent => findInference(parent.source)).take(1).toSeq.headOption
    case _                               => None
  }

  def findInference(source: Source): Option[Source.Inference] = source match {
    case inference: Source.Inference    => Some(inference)
    case Source.Internal(_, _, parents) => parents.iterator.flatMap(parent => findInference(parent.source)).take(1).toSeq.headOption
    case Source.Creator(_, _, parents)  => parents.iterator.flatMap(parent => findInference(parent.source)).take(1).toSeq.headOption
    case Source.List(sources)           => sources.iterator.flatMap(findInference).take(1).toSeq.headOption
    case _                              => None
  }

  def breakOnNestedInferences(stepName: String, source: Source): Unit = source match {
    case root: Source.Inference =>
      firstNestedInference(root).foreach { nestedInference =>
        break(Left(InferenceWithUnsupportedNestedInference(stepName, root, nestedInference)))
      }
    case _ =>
  }

  def checkUnambiguousStatus(step: ParsedTstpDerivationStep, allowedStatuses: Set[TstpStatus]): Unit = {
    if !step.annotationsOption.hasUnambiguousStatusAmong(allowedStatuses.toSeq) then
      break(Left(StepWithInvalidStatus(step.name, step.statuses, allowedStatuses.toSeq)))
  }

  derivation.stepsIterator.foreach {
    case s: ParsedTstpPlainInferenceStep => {
      checkUnambiguousStatus(s, Set(TstpStatus.Thm))
      checkNestedStatuses(s.name, s.annotations.source)
    }
    case s: ParsedTstpNegatedConjectureStep => {
      checkUnambiguousStatus(s, Set(TstpStatus.Cth))
      breakOnNestedInferences(s.name, s.annotations.source)
    }
    case s: ParsedTstpSkolemizationStep => {
      checkUnambiguousStatus(s, Set(TstpStatus.Esa))
      breakOnNestedInferences(s.name, s.annotations.source)
    }
    case _ =>
  }
  Right(())
}

def checkDerivationHasCorrectFileDirectives(derivation: StructurallyCorrectTstpDerivation, fileName: String)(using resolver: FileNameResolver): Either[TstpDerivationError, Unit] = boundary {
  val parseTptpMemoTable: scala.collection.mutable.Map[String, TptpFile] = scala.collection.mutable.Map.empty
  val proofDirectory = os.Path(fileName, os.pwd) / os.up
  derivation.stepsIterator.foreach {
    case s: FileSourceStep => {
      val (fileName, label) = (s.problemFile, s.problemFileLabel)
      val resolvedFileName =
        if Paths.get(fileName).isAbsolute() then fileName else (proofDirectory / os.RelPath(fileName)).toString
      val tptpFile = parseTptpMemoTable.getOrElseUpdate(
        fileName, {
          val tptpFileContent = resolver(resolvedFileName).getOrElse {
            break(Left(FileDirectiveFileNotFound(s.name, fileName)))
          }
          loadTptpFileWithIncludes(
            NamedTptpInputFile(resolvedFileName, tptpFileContent)
          ).left.map {
            case TptpFileLoadingError.FileNotFound(includedFileName) =>
              FileDirectiveFileNotFound(s.name, includedFileName)
            case TptpFileLoadingError.InvalidSyntax(includedFileName, cause) =>
              FileDirectiveInvalidSyntax(s.name, includedFileName, cause)
            case TptpFileLoadingError.IncludeCycle(includedFileName) => IncludeCycle(includedFileName)
          }.getOrBreak
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

      if fileDirectiveFormula.role != s.role.value then {
        break(Left(FileDirectiveStepDoesNotMatchRole(s.name, fileName, label, s.role.value, fileDirectiveFormula.role)))
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
    }
    case _ =>
  }
  Right(())
}

private object TstpCheckSyntax {
  extension (annotations: Option[Annotations])
    def hasUnambiguousStatusAmong(statuses: Seq[TstpStatus]): Boolean = boundary {
      val ann = annotations.getOrElse { break(false) }
      val inferenceSource = ann.source.asInferenceOption.getOrElse { break(false) }
      val inferenceStatus = inferenceSource.statuses.toSet.singleOption.getOrElse { break(false) }

      statuses.contains(inferenceStatus)
    }

  extension (step: ParsedTstpDerivationStep)
    def hasUnambiguousStatusAmong(statuses: Seq[TstpStatus]): Boolean = boundary {
      step.annotationsOption.hasUnambiguousStatusAmong(statuses)
    }

  extension (gt: GeneralTerm)
    def asStatus: Option[TstpStatus] = gt match {
      case TptpTerm("status", TptpTerm(value)) => Some(TstpStatus.fromValue(value))
      case _                                   => None
    }

  extension (usefulInfo: Seq[GeneralTerm])
    def statuses: Seq[TstpStatus] = usefulInfo.flatMap(_.asStatus)

  extension (inference: Source.Inference)
    def statuses: Seq[TstpStatus] = inference.usefulInfo.statuses

  extension (step: ParsedTstpDerivationStep)
    def statuses: Seq[TstpStatus] = step.annotationsOption.flatMap(_.source.asInferenceOption).map(_.statuses).getOrElse(Seq.empty)

  extension (annotatedFormula: AnnotatedFormula)
    def parentLabels: Seq[String] = annotatedFormula.annotations match {
      case None        => Seq.empty
      case Some(value) => TstpSourceSyntax.parentLabels(value.source)
    }

  extension (source: Source)
    def asInferenceOption: Option[Source.Inference] = source match {
      case s @ Source.Inference(_, _, _) => Some(s)
      case _                             => None
    }

  extension (step: ParsedTstpDerivationStep)
    def annotationsOption: Option[Annotations] = step match {
      case _: ParsedTstpConjectureStep        => None
      case _: ParsedTstpAxiomStep             => None
      case s: ParsedTstpPlainInferenceStep    => Some(s.annotations)
      case s: ParsedTstpNegatedConjectureStep => Some(s.annotations)
      case s: ParsedTstpSkolemizationStep     => Some(s.annotations)
    }

  extension [T](a: IterableOnce[T])
    def singleOption: Option[T] = a.iterator.take(2).toSeq match {
      case Seq()  => None
      case Seq(x) => Some(x)
      case _      => None
    }
}

case class InputSyntaxError(
    cause: IllegalArgumentException,
    fileName: String
) extends VerifiedUnknownReason {
  override def message: String = s"invalid TPTP syntax in $fileName: ${cause.getMessage}"
}

case class DistinctFormulasWithSameName(
    label: String,
    firstStep: ParsedTstpDerivationStep,
    duplicateStep: ParsedTstpDerivationStep
) extends VerifiedBadReason {
  override def message: String =
    s"multiple proof steps use label '$label': ${firstStep.name} has formula ${firstStep.formula}, " +
      s"while ${duplicateStep.name} has formula ${duplicateStep.formula}"
}

case class InferenceCycle(cycle: Seq[String]) extends VerifiedBadReason {
  def message: String = s"inference cycle detected: ${cycle.mkString(" -> ")}"
}

case class StepWithInvalidStatus(
    stepName: String,
    actualStatuses: Seq[TstpStatus],
    validStatuses: Seq[TstpStatus]
) extends VerifiedBadReason {
  override def message: String = {
    val actualMessage =
      if actualStatuses.isEmpty then s"$stepName has no status"
      else s"$stepName has invalid statuses ${actualStatuses.map(_.value).mkString(", ")}"
    val expectedMessage = validStatuses match {
      case Seq(status) => s"Expected only to have status ${status.value}"
      case statuses    => s"Expected one of ${statuses.map(_.value).mkString(", ")}"
    }
    s"$actualMessage. $expectedMessage"
  }
}

case class StepWithInvalidInferenceRule(
    stepName: String,
    actualInferenceName: String,
    expectedInferenceName: String
) extends VerifiedBadReason {
  override def message: String = s"$stepName has invalid inference name '$actualInferenceName'. Expected '$expectedInferenceName'"
}

case class NegatedConjectureStepWithNonConjectureParent(
    stepName: String,
    parent: ParsedTstpDerivationStep
) extends VerifiedBadReason {
  def message: String =
    s"negated conjecture step $stepName has parent ${parent.name} with role ${parent.role.value}; expected a conjecture parent"
}

case class NegatedConjectureWithoutParent(
    stepName: String
) extends VerifiedBadReason {
  def message: String = s"negated conjecture step with name $stepName has no parent"
}

case class NegatedConjectureWithMultipleDistinctParents(
    stepName: String,
    parents: Seq[String]
) extends VerifiedBadReason {
  def message: String = s"negated conjecture step $stepName has multiple distinct parents: ${parents.mkString(", ")}"
}

case class PlainInferenceWithConjectureParent(
    step: ParsedTstpDerivationStep,
    parents: Seq[ParsedTstpDerivationStep]
) extends VerifiedBadReason {
  def message: String =
    s"plain inference step ${step.name} has conjecture parent(s): ${parents.map(p => s"${p.name} (${p.role.value})").mkString(", ")}"
}

case class MultipleConjectures(
    stepNames: Seq[String]
) extends VerifiedBadReason {
  def message: String = s"derivation contains multiple conjectures: ${stepNames.mkString(", ")}"
}

case class PlainInferenceWithoutSource(
    stepName: String
) extends VerifiedBadReason {
  def message: String = s"plain inference step with name $stepName has no source"
}

case class IncorrectInference(
    stepName: String,
    sequent: Sequent[FOLFormula]
) extends VerifiedBadReason {
  def message: String = s"inference step $stepName is incorrect. the corresponding sequent is not valid: $sequent"
}

case class IncorrectSkolemization(
    reason: IncorrectSkolemizationReason
) extends VerifiedBadReason {
  def message: String = reason.message
}

case class NonConstantSkolemTerm(
    stepName: String,
    term: FOLVar
) extends VerifiedBadReason {
  def message: String = s"step $stepName: skolem term $term is not a constant, but a variable"
}

case class SkolemizationStepWithoutParent(
    stepName: String
) extends VerifiedBadReason {
  def message: String = s"skolemization inference with name $stepName has no parent"
}

case class SkolemizationStepWithMultipleParents(
    stepName: String,
    parents: Seq[String]
) extends VerifiedBadReason {
  def message: String = s"skolemization inference with name $stepName has multiple parents ${parents.mkString(", ")}"
}

case class NonExistentStep(
    stepName: String,
    referencedByStepName: String
) extends VerifiedBadReason {
  def message: String = s"step $referencedByStepName refers to missing parent step $stepName"
}

sealed trait IncorrectSkolemizationReason {
  def message: String
}

case class BoundVariableMismatch(
    stepName: String,
    claimedBoundVariable: FOLVar,
    actualBoundVariable: FOLVar,
    parentFormula: FOLFormula
) extends IncorrectSkolemizationReason {
  def message: String = s"skolemization step $stepName claims to skolemize bound variable $claimedBoundVariable, but the actual quantified variable in $parentFormula is $actualBoundVariable"
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
    stepDefinitions: SeqMap[String, VerifiedSkolemization]
) extends IncorrectSkolemizationReason {
  def message: String = s"skolem symbol $skolemSymbol is introduced multiple times with conflicting definitions: ${stepDefinitions.map { case (step, skolemization) => s"in $step defined as skolem symbol ${skolemization.skolemSymbol} with ${skolemization.skolemDefinition}" }.mkString("; ")}"
}

case class SkolemDependency(
    stepName: String,
    skolemSymbol: String,
    dependsOnStepName: String,
    dependencySymbol: String
)

case class CyclicSkolemDefinitions(dependencies: Seq[SkolemDependency]) extends IncorrectSkolemizationReason {
  def message: String =
    s"cyclic Skolem definitions: ${dependencies.map(d => s"step '${d.stepName}' defines '${d.skolemSymbol}', which depends on '${d.dependencySymbol}' defined by step '${d.dependsOnStepName}'").mkString("; ")}"
}

case class SkolemSymbolIsAConstantExistingInTheInput(
    inputStepName: String,
    skolemizationStepName: String,
    const: Const
) extends IncorrectSkolemizationReason {
  def message: String = s"skolemization step $skolemizationStepName introduces skolem symbol $const that is already used in the input in step $inputStepName"
}

case class SkolemSymbolWithDifferentArity(
    skolemizationStepName: String,
    skolemSymbol: Const,
    occurrenceStepName: String,
    occurrence: Const
) extends IncorrectSkolemizationReason {
  def message: String = s"skolemization step $skolemizationStepName introduces skolem symbol $skolemSymbol, but step $occurrenceStepName uses $occurrence with the same name and a different arity"
}

case class SkolemSymbolWithDifferentArities(
    skolemSymbol: String,
    declarations: SeqMap[String, Const]
) extends IncorrectSkolemizationReason {
  def message: String = s"skolem symbol $skolemSymbol is introduced with different arities: ${declarations.map { case (step, symbol) => s"$step: $symbol" }.mkString(", ")}"
}

case class NonRectifiedFormula(
    stepName: String,
    formula: FOLFormula
) extends IncorrectSkolemizationReason {
  def message: String = s"skolemization step $stepName has non-rectified parent formula $formula (contains different quantifiers with the same bound variable)"
}

case class SkolemizationStepWithNewSymbolDifferingFromSkolemizeTerm(
    stepName: String,
    declaredSymbol: Const,
    termSymbol: Const
) extends VerifiedBadReason {
  def message: String =
    s"skolemization step $stepName declares new symbol $declaredSymbol, but its skolemize term uses $termSymbol"
}

case class SkolemizationStepWithoutNewSymbols(
    stepName: String
) extends VerifiedBadReason {
  def message: String = s"skolemization step with name $stepName has no new symbols"
}

case class SkolemizationStepWithoutBinding(
    stepName: String
) extends VerifiedBadReason {
  def message: String = s"skolemization step with name $stepName has no skolemize(_,_) binding"
}

case class CannotHandleIncludeDirectives() extends VerifiedUnknownReason {
  def message: String = "cannot handle include directives"
}

case class IncludeFileNotFound(fileName: String) extends VerifiedUnknownReason {
  def message: String = s"included file not found: $fileName"
}

case class IncludeInvalidSyntax(fileName: String, cause: IllegalArgumentException) extends VerifiedUnknownReason {
  def message: String = s"included file has invalid TPTP syntax in $fileName: ${cause.getMessage}"
}

case class IncludeCycle(fileName: String) extends VerifiedUnknownReason {
  def message: String = s"include cycle detected at $fileName"
}

case class CannotHandleInput(stepName: String, reason: String) extends VerifiedUnknownReason {
  def message: String = s"cannot handle input step with name $stepName: $reason"
}

case class PlainInferenceWithNonThmNestedInference(stepName: String, inference: Source.Inference) extends VerifiedUnknownReason {
  def message: String = s"step $stepName has an inference parent with a non-thm status: $inference"
}

case class InferenceWithUnsupportedNestedInference(
    stepName: String,
    rootInference: Source.Inference,
    inlineInference: Source.Inference
) extends VerifiedUnknownReason {
  def message: String = s"step $stepName has inline inference $inlineInference under non-thm root inference $rootInference"
}

case class NoRefutationFound() extends VerifiedBadReason {
  def message: String = "no refutation found: the derivation has no non-conjecture root $false formula"
}

case class UnexpectedInput(message: String) extends VerifiedUnknownReason

case class NoStrongQuantifierFittingSkolemization(stepName: String, inputFormula: FOLFormula, skolemizedFormula: FOLFormula, skVar: FOLVar, skTerm: FOLTerm)
    extends IncorrectSkolemizationReason {
  def message: String = s"skolemization step $stepName: could not find a strong quantifier s.t. replacing $skVar with $skTerm transforms $inputFormula into $skolemizedFormula!"
}

case class MultipleStrongQuantifiersFittingSkolemization(stepName: String, inputFormula: FOLFormula, skolemizedFormula: FOLFormula, skVar: FOLVar, skTerm: FOLTerm)
    extends IncorrectSkolemizationReason {
  def message: String = s"could find multiple (non-unique) strong quantifiers s.t. replacing $skVar with $skTerm transforms $inputFormula into $skolemizedFormula!"
}

sealed trait FileDirectiveError extends VerifiedBadReason
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

case class FileDirectiveInvalidSyntax(
    stepName: String,
    fileName: String,
    cause: IllegalArgumentException
) extends FileDirectiveError {
  override def message: String =
    s"step $stepName has a file source ($fileName) with invalid TPTP syntax: ${cause.getMessage}"
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

case class FileNotFound(fileName: String) extends VerifiedUnknownReason {
  override def message: String = s"file not found: $fileName"
}

case class UnexpectedException(e: Throwable) extends VerifiedUnknownReason {
  override def message: String = {
    val details = Option(e.getMessage).filter(_.nonEmpty).fold(e.toString)(identity)
    s"unexpected exception ${e.getClass.getName}: $details"
  }
}
