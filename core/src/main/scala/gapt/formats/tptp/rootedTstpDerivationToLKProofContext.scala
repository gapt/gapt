package gapt.formats.tptp

import gapt.expr.{Abs, Const, Expr, Var, substitute, given}
import gapt.expr.formula.*
import gapt.expr.formula.fol.{FOLAtom, FOLConst, FOLFormula, FOLFunctionConst, FOLTerm, FOLVar}
import gapt.expr.formula.hol.HOLPosition
import gapt.expr.ty.Ti
import gapt.expr.util.{constants, freeVariables}
import gapt.formats.tptp.*
import gapt.logic.Polarity
import gapt.proofs.Ant
import gapt.proofs.Sequent
import gapt.proofs.context.{Context, State}
import gapt.proofs.context.facet.ProofNames
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.{ProofDefinitionDeclaration, ProofNameDeclaration, Sort, Update}
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.{AndLeftRule, AndRightRule, CutRule, ExistsLeftRule, ExistsRightRule, ExistsSkLeftRule, ForallLeftRule, ForallRightRule, ForallSkRightRule, ImpLeftRule, ImpRightRule, LogicalAxiom, NegLeftRule, NegRightRule, OrLeftRule, OrRightRule, ProofLink, WeakeningLeftRule}
import gapt.proofs.lk.rules.macros.ForallLeftBlock
import gapt.proofs.lk.rules.macros.ForallRightBlock
import gapt.provers.ResolutionProver
import gapt.provers.escargot.Escargot
import gapt.utils.Maybe
import gapt.utils.getOrBreak
import gapt.proofs.context.immutable.ImmutableContext
import gapt.logic.hol.SkolemFunctions
import gapt.proofs.Suc

import scala.util.boundary
import boundary.break
import scala.util.boundary.Label
import gapt.formats.tptp.FindSkolemizableInstance.QuantifierType.{Strong, Weak}
import gapt.logic.Polarity.{Negative, Positive}


case class VariableCapturingProofDeclaration(lhs: Expr, proof: LKProof) extends Update {
  def link = ProofLink(lhs, proof.endSequent)

  override def apply(ctx: Context): State =
    ctx + ProofNameDeclaration(lhs, proof.endSequent, freeVariables(proof.endSequent)) + ProofDefinitionDeclaration(lhs, proof) state

  override def toString: String =
    s"VariableCapturingProofDeclaration($lhs, ${proof.endSequent})"
}

/**
* Attempts to replay the inferences in the given RootedTstpDerivation into a Context and a ProofLink
* such that instantiating the ProofLink in the context gives the full LKProof.
*/
def rootedTstpDerivationToLKProofContext(
    derivation: RootedTstpDerivation,
    prover: ResolutionProver = Escargot
): Either[IncorrectInference | IncorrectSkolemization, (ProofLink, Context)] = boundary { outer ?=>
  val (ctx, verifiedSkolemizationsByStepName) = constructTstpDerivationContext(derivation).getOrBreak
  given context: MutableContext = ctx.newMutable

  def replayProof(inferenceName: String, sequentToProve: Sequent[FOLFormula]): LKProof = {
    prover.getLKProof(sequentToProve).getOrElse {
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

  derivation.stepsTopologicallyOrderedFromLeafsToRoot.foreach { s =>
    s match {
      case _: TstpConjectureStep =>
      case s: TstpAxiomStep => {
        context += proofDeclaration(s.name, LogicalAxiom(s.formula), Seq.empty)
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

        context += proofDeclaration(s.name, cutProof, Seq.empty)
      }

      case s: TstpSkolemizationStep => {
        val skolemizationStep = verifiedSkolemizationsByStepName(s.name)
        context += proofDeclaration(s.name, skolemizationStep.proof, Seq(s.parent))
      }

      case s: TstpPlainInferenceStep => {
        val parentFormulas = s.parents.map(p => derivation.get(p).get.formula)
        val sequentToProve = Sequent(parentFormulas, Vector(s.formula))
        val proof = replayProof(s.name, sequentToProve)
        context += proofDeclaration(s.name, proof, s.parents)
      }
    }
  }

  val proofLink = ProofLink(derivation.root.name)(using context)
  Right((proofLink, context.toImmutable))
}

private def constructTstpDerivationContext(
    derivation: RootedTstpDerivation
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
private case class VerifiedSkolemization private (
    skolemSymbol: SkolemSymbol,
    skolemDefinition: SkolemDefinition,
    proof: LKProof
)

object VerifiedSkolemization {
  def fromTstpSkolemizationStepAndParentFormula(
                                                 skolemizationStep: TstpSkolemizationStep,
                                                 parentFormula: FOLFormula
                                               ): Either[IncorrectSkolemization, VerifiedSkolemization] = boundary {
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
      reportIncorrectSkolemization(NonRectifiedFormula(name, parentFormula))
    }

    val claimedSkolemTerm = newSkolemSymbol(claimedContextVariables *)
    val pol = Negative //TODO: we are assuming a negative context (i.e. if coming from an conjecture leaf, there was negated_conjecture before)
    val possible_matches = FindSkolemizableInstance(parentFormula, claimedSkolemizedFormula, pol, claimedBoundVariable, newSkolemSymbol, claimedSkolemTerm)
    if possible_matches.size == 0 then {
      reportIncorrectSkolemization(NoStrongQuantifierFittingSkolemization(name, parentFormula, claimedSkolemizedFormula, claimedBoundVariable, claimedSkolemTerm))
    }
    if possible_matches.size > 1 then {
      reportIncorrectSkolemization(MultipleStrongQuantifiersFittingSkolemization(name, parentFormula, claimedSkolemizedFormula, claimedBoundVariable, claimedSkolemTerm))
    }
    val (q_pos, sk_context, parent_context) = possible_matches(0)

    val actualContextVariables = sk_context collect { case (Weak, x) => x.asInstanceOf[FOLVar] }

    if actualContextVariables.distinct != actualContextVariables then {
      reportIncorrectSkolemization(NonRectifiedFormula(name, parentFormula))
    }

    if actualContextVariables contains claimedBoundVariable then {
      reportIncorrectSkolemization(NonRectifiedFormula(name, parentFormula))
    }


    if claimedContextVariables != actualContextVariables then {
      reportIncorrectSkolemization(ContextVariableMismatch(name, claimedContextVariables, actualContextVariables, claimedBoundVariable, parentFormula))
    }

    val mainSkolemizationFormula = HOLPosition.toLambdaPosition(parentFormula)(q_pos).get(parentFormula).get.asInstanceOf[FOLFormula] //TODO: remove this ugly cast
    val skolemDefinition = Abs.Block(actualContextVariables, mainSkolemizationFormula)

    val innerFormula = mainSkolemizationFormula match {
      case All(_, f) => f
      case Ex(_, f) => f
    }

    val innerSubstituted = innerFormula.substitute(claimedBoundVariable -> claimedSkolemTerm)
//    println(s"Creating proof for: $parentFormula $claimedSkolemizedFormula $claimedBoundVariable $claimedSkolemTerm")
    val skolemizationProof = CreateSkolemizationProof(parentFormula, claimedSkolemizedFormula, claimedBoundVariable, claimedSkolemTerm, q_pos, pol)
    Right(new VerifiedSkolemization(newSkolemSymbol, skolemDefinition, skolemizationProof))
    //    val All.Block(actualContextVariables, mainSkolemizationFormula) = parentFormula
    //
    //    if actualContextVariables.distinct != actualContextVariables then {
    //      reportIncorrectSkolemization(NonRectifiedFormula(name, parentFormula))
    //    }
    //
    //    val (actualBoundVariable, innerSkolemizationFormula) = mainSkolemizationFormula match {
    //      case Ex(actualBoundVariable, inner) => (actualBoundVariable, inner)
    //      case f =>
    //        reportIncorrectSkolemization(NoExistentialQuantifierAfterRootUniversalBlock(name, claimedBoundVariable, f, parentFormula))
    //    }
    //
    //    if claimedBoundVariable != actualBoundVariable then {
    //      reportIncorrectSkolemization(BoundVariableMismatch(name, claimedBoundVariable, actualBoundVariable, parentFormula))
    //    }
    //
    //    if claimedContextVariables != actualContextVariables then {
    //      reportIncorrectSkolemization(ContextVariableMismatch(name, claimedContextVariables, actualContextVariables, claimedBoundVariable, parentFormula))
    //    }
    //
    //    val claimedSkolemTerm = newSkolemSymbol(claimedContextVariables*)
    //    val innerSubstituted = innerSkolemizationFormula.substitute(claimedBoundVariable -> claimedSkolemTerm)
    //    val expectedSkolemizedFormula = All.Block(actualContextVariables, innerSubstituted)
    //
    //    if expectedSkolemizedFormula != claimedSkolemizedFormula then {
    //      reportIncorrectSkolemization(FormulaMismatch(name, claimedSkolemizedFormula, claimedBoundVariable, claimedSkolemTerm, expectedSkolemizedFormula, parentFormula))
    //    }
    //    val skolemDefinition = Abs.Block(actualContextVariables, mainSkolemizationFormula)
    //
    //    val axiom = LogicalAxiom(innerSubstituted)
    //    val existsSkLeft = ExistsSkLeftRule(axiom, Ant(0), mainSkolemizationFormula, claimedSkolemTerm)
    //    val forallLeft = ForallLeftBlock(existsSkLeft, parentFormula, actualContextVariables)
    //    val skolemizationProof = ForallRightBlock(forallLeft, expectedSkolemizedFormula, actualContextVariables)
    //
    //    Right(new VerifiedSkolemization(newSkolemSymbol, skolemDefinition, skolemizationProof))
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
    derivation: RootedTstpDerivation,
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
      val leftDefinition = leftSkolemization.skolemDefinition
      val rightSymbol = rightSkolemization.skolemSymbol
      val rightDefinition = rightSkolemization.skolemDefinition
      assert(leftSymbol.name == rightSymbol.name, s"skolem symbol names do not match: ${leftSymbol.name} != ${rightSymbol.name}")
      if leftDefinition == rightDefinition then acc
      else acc ++ Set((leftStep, leftSkolemization), (rightStep, rightSkolemization))
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
   * Finds all positions p and variable contects s.t. unskolemized[p] is a strongly quantified
   * formula Q skVar . F and replacing unskolemized[p] by F{skVar <- skTerm} obtains skolemized.
   */
  def apply(unskolemized: FOLFormula, skolemized: FOLFormula, polarity: Polarity, skVar : FOLVar, skConst : Const, skTerm : FOLTerm) = {
    def skQuantifier(e : Expr) = e match { case All(x, _) => skVar == x; case Ex(x, _) => skVar == x; case _ => false}
    val candidate_positions = HOLPosition.getPositions(unskolemized, skQuantifier)
    val qs = candidate_positions filter (x => isStrongQuantifierPosition(x, unskolemized, polarity))
    //println(s"us: $unskolemized s: $skolemized candidates: $candidate_positions strong_qs: $qs")
    val correctly_skolemized = qs filter (pos => {
      val inner_pos = HOLPosition(pos.list :+ 1)
      val lambda_pos = HOLPosition.toLambdaPosition(unskolemized)(inner_pos)
      val body = lambda_pos.get(unskolemized).get
      val reskolemized = HOLPosition.replace(unskolemized, pos, body.substitute(skVar -> skTerm))
//      println(s"$skolemized == $reskolemized")
      reskolemized == skolemized
    })
    def getContext(x:HOLPosition,f:FOLFormula) = polarityAndContextAt(x, f, polarity)._2
    correctly_skolemized map (x => (x, getContext(x, skolemized), getContext(x, unskolemized)))
  }

  def polarityAndContextAt(pos: HOLPosition, e: Expr, polarity: Polarity, context:List[(QuantifierType, Var)] = Nil): (Polarity, List[(QuantifierType, Var)]) =
    (pos.list, e) match {
      case (Nil, _) => (polarity, context.reverse)
      case (_, FOLAtom(_, _)) => (polarity, context.reverse)
      case (1 :: _, Neg(x)) => polarityAndContextAt(pos.tail, x, !polarity, context)
      case (1 :: _, All(v, x)) =>
        val ws = if polarity == Positive then Strong else Weak
        polarityAndContextAt(pos.tail, x, polarity, (ws, v) :: context)
      case (1 :: _, Ex(v, x)) =>
        val ws = if polarity == Positive then Weak else Strong
        polarityAndContextAt(pos.tail, x, polarity, (ws, v) :: context)
      case (1 :: _, And(x, _)) => polarityAndContextAt(pos.tail, x, polarity, context)
      case (2 :: _, And(_, x)) => polarityAndContextAt(pos.tail, x, polarity, context)
      case (1 :: _, Or(x, _)) => polarityAndContextAt(pos.tail, x, polarity, context)
      case (2 :: _, Or(_, x)) => polarityAndContextAt(pos.tail, x, polarity, context)
      case (1 :: _, Imp(x, _)) => polarityAndContextAt(pos.tail, x, !polarity, context)
      case (2 :: _, Imp(_, x)) => polarityAndContextAt(pos.tail, x, polarity, context)
      case _ => throw new Exception(s"Could not find polarity of $pos in $e")
    }


  def isStrongQuantifierPosition(pos : HOLPosition, e : Expr, polarity: Polarity) : Boolean = {
    val pol = polarityAndContextAt(pos, e, polarity)._1
    val lambda_pos = HOLPosition.toLambdaPosition(e)(pos)
    lambda_pos.get(e) match {
      case Some(All(_,_)) => pol == Positive
      case Some(Ex(_,_)) => pol == Negative
      case _ => false
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
  def apply(unskolemized : FOLFormula, skolemized : FOLFormula, skVar : FOLVar, skTerm : FOLTerm, pathToSk: HOLPosition, polarity: Polarity) : LKProof = {
    if unskolemized == skolemized then
      LogicalAxiom(unskolemized)
    if pathToSk.isEmpty then {
      val axiom = LogicalAxiom(skolemized)
      if polarity == Negative then
        ExistsSkLeftRule(axiom, Ant(0), unskolemized, skTerm)
      else
        ForallSkRightRule(axiom, Suc(0), unskolemized, skTerm)
    }
    else {
      val branch = pathToSk.head
      val remainingBranch = pathToSk.tail
      // polarity swaps on which side the unskolemized and skolemized formula appear (neg: skolemized right, pos: skolemized left)
      def swapPos(a:FOLFormula, b:FOLFormula) = if polarity == Negative then (a,b) else (b,a)

      (unskolemized, skolemized, branch) match {
        case (a @ Neg(f), sa @ Neg(fs), 1) =>
          val rp = apply(f, fs, skVar, skTerm, remainingBranch, !polarity)
          val (b, sb) = swapPos(a, sa)
          val p1 = NegLeftRule(rp, sb)
          NegRightRule(p1, b)
        case (a @ And(f, g), sa @ And(fs, _), 1) =>
          val rp = apply(f, fs, skVar, skTerm, remainingBranch, polarity)
          val axiom = LogicalAxiom(g)
          val (b, sb) = swapPos(a, sa)
          val p1 = AndRightRule(rp, axiom, sb)
          AndLeftRule(p1, b)
        case (a @ And(f, g), sa @ And(_,gs), 2) =>
          val axiom = LogicalAxiom(f)
          val rp = apply(g, gs, skVar, skTerm, remainingBranch, polarity)
          val (b, sb) = swapPos(a, sa)
          val p1 = AndRightRule(axiom, rp, sb)
          AndLeftRule(p1, b)
        case (a @ Or(f, g), sa @ Or(fs, _), 1) =>
          val rp = apply(f, fs, skVar, skTerm, remainingBranch, polarity)
          val axiom = LogicalAxiom(g)
          val (b, sb) = swapPos(a, sa)
          val p1 = OrLeftRule(rp, axiom, b)
          OrRightRule(p1, sb)
        case (a @ Or(f, g), sa @ Or(_, gs), 2) =>
          val rp = apply(g, gs, skVar, skTerm, remainingBranch, polarity)
          val axiom = LogicalAxiom(f)
          val (b, sb) = swapPos(a, sa)
          val p1 = OrLeftRule(axiom, rp, b)
          OrRightRule(p1, sb)
        case (a @ Imp(f, g), sa @ Imp(fs, _), 1) =>
          val rp = apply(f, fs, skVar, skTerm, remainingBranch, !polarity)
          val axiom = LogicalAxiom(g)
          val (b, sb) = swapPos(a, sa)
          val p1 = ImpLeftRule(rp, axiom, b)
          ImpRightRule(p1, sb)
        case (a @ Imp(f, g), sa @ Imp(_, gs), 2) =>
          val rp = apply(g, gs, skVar, skTerm, remainingBranch, polarity)
          val axiom = LogicalAxiom(f)
          val (b, sb) = swapPos(a, sa)
          val p1 = ImpLeftRule(axiom, rp, b)
          ImpRightRule(p1, sb)
        case (a @ All(x,f), sa @ All(y,fs), 1) =>
          val rp = apply(f, fs, skVar, skTerm, remainingBranch, polarity)
          val (b, sb) = swapPos(a, sa)
          val p1 = ForallLeftRule(rp, b)
          ForallRightRule(p1, sb)
        case (a @ Ex(x,f), sa @ Ex(y,fs), 1) =>
          val rp = apply(f, fs, skVar, skTerm, remainingBranch, polarity)
          val (b, sb) = swapPos(a, sa)
          val p1 = ExistsRightRule(rp, sb)
          ExistsLeftRule(p1, b)
        case _ =>
          throw IllegalArgumentException(s"Unhandled case ($unskolemized, $skolemized, $pathToSk, $polarity)")
      }
    }


  }

}
