package gapt.provers.viper.grammars

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.fol.{flatSubterms, folTermSize}
import gapt.expr.formula.hol._
import gapt.expr.subst.Substitution
import gapt.expr.ty.TBase
import gapt.expr.ty.To
import gapt.expr.ty.Ty
import gapt.expr.util.expressionSize
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.formats.babel.BabelSignature
import gapt.formats.latex.LatexExporter
import gapt.formats.smt.SmtLibExporter
import gapt.grammars.{InductionGrammar, findMinimalInductionGrammar}
import gapt.grammars.InductionGrammar.Production
import gapt.logic.hol.CNFp
import gapt.logic.hol.dls.dls
import gapt.logic.hol.skolemize
import gapt.proofs.context.Context
import gapt.proofs.context.facet.{BaseTypes, StructurallyInductiveTypes}
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.expansion.{ExpansionProof, InstanceTermEncoding, freeVariablesET, minimalExpansionSequent}
import gapt.proofs.gaptic.Tactical1
import gapt.proofs.lk.{LKProof, lkProofReplaceable}
import gapt.proofs.lk.util.EquationalLKProver
import gapt.proofs.{HOLSequent, Sequent, withSection, RichFormulaSequent}
import gapt.provers.escargot.{Escargot, QfUfEscargot}
import gapt.provers.maxsat.{MaxSATSolver, bestAvailableMaxSatSolver}
import gapt.provers.verit.VeriT
import gapt.provers.{OneShotProver, Prover}
import gapt.utils.{Logger, Maybe, TimeOutException}
import gapt.utils._
import org.apache.commons.lang3.exception.ExceptionUtils

import scala.collection.mutable
import scala.util.Failure
import scala.util.Success

object DefaultProvers {
  val firstOrder: Prover = Escargot
  val smt: Prover = if (VeriT.isInstalled) VeriT else QfUfEscargot
}

import TreeGrammarProverOptions._

case class TreeGrammarProverOptions(
    goalQuantifier: Int = 0,
    instanceNumber: Int = 10,
    instanceSize: FloatRange = (0, 2),
    instanceProver: Prover = DefaultProvers.firstOrder,
    minInstProof: Boolean = true,
    smtSolver: Prover = DefaultProvers.smt,
    smtEquationMode: SmtEquationMode = AddNormalizedFormula,
    quantTys: Option[Seq[TBase]] = None,
    grammarWeighting: ProductionWeight = NumProductionsWeight,
    tautCheckNumber: Int = 10,
    tautCheckSize: FloatRange = (2, 3),
    bupSolver: InductionBupSolver = InductionBupSolver.Canonical,
    canSolSize: FloatRange = (2, 4),
    maxSATSolver: MaxSATSolver = bestAvailableMaxSatSolver,
    equationalTheory: Seq[Formula] = Seq()
)

sealed trait InductionBupSolver
object InductionBupSolver {
  case object Interpolation extends InductionBupSolver
  case object Canonical extends InductionBupSolver
  case object Dls extends InductionBupSolver
}

object TreeGrammarProverOptions {
  type FloatRange = (Float, Float)

  trait SmtEquationMode { def adapt(th: Seq[Formula], p: Prover): Prover }
  case object AddNormalizedFormula extends SmtEquationMode {
    override def adapt(th: Seq[Formula], p: Prover): Prover =
      new OneShotProver {
        override def getLKProof(seq: HOLSequent)(implicit ctx: Maybe[MutableContext]): Option[LKProof] =
          throw new NotImplementedError

        val eqTh = Normalizer(th.map(ReductionRule(_)))
        override def isValid(seq: HOLSequent)(implicit ctx: Maybe[Context]): Boolean =
          p.isValid(seq ++ seq.map(eqTh.normalize(_).asInstanceOf[Formula]))
      }
  }
  case object Passthru extends SmtEquationMode {
    override def adapt(th: Seq[Formula], p: Prover): Prover =
      new OneShotProver {
        override def getLKProof(seq: HOLSequent)(implicit ctx: Maybe[MutableContext]): Option[LKProof] =
          throw new NotImplementedError

        val eqTh: Seq[Formula] = th.map(universalClosure(_))
        override def isValid(seq: HOLSequent)(implicit ctx: Maybe[Context]): Boolean =
          p.isValid(eqTh ++: seq)
      }
  }

  trait ProductionWeight {
    def apply(p: Production): Int
  }
  case object NumProductionsWeight extends ProductionWeight {
    override def apply(p: Production): Int = 1
  }
  case object SymbolicWeight extends ProductionWeight {
    override def apply(p: Production): Int = folTermSize(p.lhs) + folTermSize(p.rhs)
  }
}

object TreeGrammarProver {
  val logger = Logger("TreeGrammarProver")

  def apply(sequent: HOLSequent, options: TreeGrammarProverOptions = TreeGrammarProverOptions())(implicit ctx: Context): LKProof =
    new TreeGrammarProver(ctx, sequent, options).solve()
}

class TreeGrammarProver(val ctx: Context, val sequent: HOLSequent, val options: TreeGrammarProverOptions) {
  import TreeGrammarProver.logger._

  implicit def ctx_ : Context = ctx

  val Sequent(theory, Seq(quantGoal @ All(v0, _))) = sequent: @unchecked
  require(!containsQuantifierOnLogicalLevel(instantiate(quantGoal, v0)))

  val indTy = v0.ty.asInstanceOf[TBase]

  val quantTys = options.quantTys.getOrElse(
    ctx.get[BaseTypes].baseTypes.values.toSet - To
  ).toList
  metric("quant_tys", quantTys)
  val gamma =
    if (quantTys.length == 1) List(Var("γ", quantTys.head))
    else
      for ((t, i) <- quantTys.zipWithIndex) yield Var(s"γ_$i", t)

  val (tau, alpha, nus) = {
    val defaultNames = InductionGrammar.defaultNonTerminalNames(
      rename.awayFrom(containedNames(sequent) ++ gamma),
      indTy,
      InstanceTermEncoding.defaultType,
      gamma
    )
    (defaultNames.tau, defaultNames.alpha, defaultNames.nus)
  }

  val goal = instantiate(quantGoal, alpha)

  val encoding = InstanceTermEncoding(sequent.map(identity, instantiate(_, alpha)))

  val instanceGen = new EnumeratingInstanceGenerator(Seq(indTy), true, implicitly)

  type Instance = Expr

  val smtSolver: Prover =
    if (options.equationalTheory.isEmpty) options.smtSolver
    else options.smtEquationMode.adapt(options.equationalTheory, options.smtSolver)

  def solve(): LKProof = time("ceggr") {
    info(sequent.toSigRelativeString)

    val instanceProofs = mutable.Map[Instance, ExpansionProof]()
    for (Seq(inst) <- instanceGen.generate(options.instanceSize._1, options.instanceSize._2, options.instanceNumber))
      instanceProofs(inst) = getInstanceProof(inst)

    def loop(iter: Int): LKProof = {
      metric("ceggr_iters", iter)
      val bup = findBUP(instanceProofs)

      for ((inst, _) <- instanceProofs) {
        val genLang = bup.grammar.instanceLanguage(inst)
        require(
          quiet(smtSolver.isValid(encoding.decodeToInstanceSequent(genLang).toNegConjunction -->
            instantiate(quantGoal, inst))),
          s"Generated instance language for $inst not tautological:\n${genLang.map(_.toSigRelativeString).mkString("\n")}"
        )
      }

      findMinimalCounterexample(instanceProofs.keys, bup) match {
        case Some(inst) =>
          instanceProofs(inst) = getInstanceProof(inst)
          loop(iter + 1)

        case None =>
          metric("candidate_grammar_found", true)
          val solution = solveBUP(bup)
          constructProof(bup, solution)
      }
    }
    loop(1)
  }

  def findBUP(instanceProofs: Iterable[(Instance, ExpansionProof)]): InductionBUP = time("grammar") {
    val indexedTermset = Map() ++
      instanceProofs.map { case (inst, es) => inst -> encoding.encode(es.expansionSequent.copy(succedent = Vector())) }

    metric("itermset_size", indexedTermset.view.flatMap(_._2).toSet.size)

    val grammar = findMinimalInductionGrammar(
      indexedTermset,
      tau,
      alpha,
      nus,
      gamma,
      options.maxSATSolver,
      options.grammarWeighting(_)
    )
      .getOrElse {
        metric("uncoverable_grammar", true)
        throw new Exception(s"cannot cover termset\n" +
          indexedTermset.map {
            case (i, ts) =>
              s"${i.toUntypedString}\n" + ts.map("  " + _.toUntypedString + "\n").mkString
          }.mkString("\n"))
      }

    info(s"Found grammar:\n$grammar\n")
    for ((inst, terms) <- indexedTermset) {
      val genLang = grammar.instanceLanguage(inst)
      require(
        terms subsetOf genLang,
        s"Terms not covered by induction grammar in $inst:\n${terms.map(_.toSigRelativeString).mkString("\n")}"
      )
    }
    metric("grammarsize", grammar.size)
    metric("num_gamma_prods", grammar.gammaProductions.size)

    InductionBUP(grammar, encoding, goal)
  }

  def findMinimalCounterexample(correctInstances: Iterable[Instance], bup: InductionBUP): Option[Expr] = time("mincex") {
    def checkInst(inst: Instance): Boolean =
      quiet(smtSolver.isValid(encoding.decodeToInstanceSequent(bup.grammar.instanceLanguage(inst)).toNegConjunction -->
        instantiate(quantGoal, inst)))
    val scale = (5 +: correctInstances.toSeq.map(folTermSize(_))).max
    val testInstances =
      (instanceGen.generate(0, 5, 10) ++
        instanceGen.generate(options.tautCheckSize._1 * scale, options.tautCheckSize._2 * scale, options.tautCheckNumber)).map(_.head)
    metric("mincex_num_cex", testInstances.size)
    val failedInstOption = testInstances.toSeq.sortBy(folTermSize(_)).view.filterNot { inst =>
      val ok = checkInst(inst)
      info(s"Checking validity for instance ${inst.toSigRelativeString}: $ok")
      ok
    }.headOption
    failedInstOption map { failedInst =>
      val minimalCounterExample = (
        flatSubterms(failedInst).filter(_.ty == indTy).toList.filterNot(checkInst)
          :+ failedInst
      ).minBy(expressionSize(_))
      info(s"Minimal counterexample: ${minimalCounterExample.toSigRelativeString}")
      minimalCounterExample
    }
  }

  def solveBUP(bup: InductionBUP): Expr = time("solvebup") {
    val qbup @ Ex(x_B, qbupMatrix) = bup.formula: @unchecked
    info(s"Solution condition:\n${qbup.toSigRelativeString}\n")
    try {
      info(s"latex:\n${LatexExporter(qbup)}\n")
      info(s"smt-lib:\n${SmtLibExporter.bup(bup.formula)}")
    } catch { case e: Throwable => info(ExceptionUtils.getStackTrace(e)) }

    val solution =
      options.bupSolver match {
        case InductionBupSolver.Interpolation =>
          solveBupViaInterpolationConcreteTerms(bup, instanceGen.terms.map(_._1).filter(_.ty == indTy))
        case InductionBupSolver.Canonical =>
          val canSolInst = instanceGen.generate(options.canSolSize._1, options.canSolSize._2, 1).head.head
          val xInst = bup.X(alpha, canSolInst)(gamma).asInstanceOf[Formula]

          info(s"Canonical solution at ${xInst.toSigRelativeString}:")
          val canSol = hSolveQBUP.canonicalSolution(qbupMatrix, xInst)
          for (cls <- CNFp(canSol))
            info(cls map { _.toSigRelativeString })

          hSolveQBUP(qbupMatrix, xInst, smtSolver, options.equationalTheory).getOrElse {
            metric("bup_solve_failed", true)
            throw new IllegalArgumentException(s"Could not solve:\n${qbupMatrix.toSigRelativeString}")
          }
        case InductionBupSolver.Dls =>
          val p = bup.formula
          dls(p) match {
            case Success((s, _)) => s(bup.X)
            case Failure(e) =>
              throw new IllegalArgumentException(s"Could not solve BUP ${bup}", e)
          }
      }

    info(s"Found solution: ${solution.toSigRelativeString}\n")

    val formula = BetaReduction.betaNormalize(instantiate(qbup, solution))
    metric("solution", solution.toSigRelativeString)
    require(smtSolver.isValid(skolemize(formula))(ctx = Maybe.None), "Solution not valid")

    solution
  }

  def constructProof(bup: InductionBUP, solution: Expr): LKProof = time("constructproof") {
    val proof = constructSIP(
      sequent,
      options.equationalTheory.toVector,
      bup,
      solution,
      if (options.equationalTheory.isEmpty) EquationalLKProver else Escargot
    )(ctx.newMutable)
    info(s"Found proof with ${proof.dagLike.size} inferences")
    metric("ind_pr_size", proof.dagLike.size)

    ctx.check(proof)

    proof
  }

  // TODO: make less hacky
  def mkGroundTerm(ty: Ty): Expr =
    ctx.constants.find(_.ty == ty).getOrElse(
      instanceGen.terms.view.map(_._1).find(_.ty == ty).head
    )

  def getInstanceProof(inst: Instance): ExpansionProof = time("instproof") {
    info(s"Proving instance ${inst.toSigRelativeString}")
    val instanceSequent = sequent.map(identity, instantiate(_, inst))
    val instProof0 = quiet(options.instanceProver.getExpansionProof(instanceSequent)).getOrElse {
      throw new IllegalArgumentException(s"Cannot prove:\n$instanceSequent")
    }
    val Some(instProof) = (if (!options.minInstProof) Some(instProof0)
                           else minimalExpansionSequent(instProof0, smtSolver)): @unchecked
    require(
      smtSolver.isValid(instProof.deep),
      s"Instance proof has invalid deep formula:\n${instProof.deep.toSigRelativeString}"
    )
    info(s"Instance proof for ${inst.toSigRelativeString}:")
    info(instProof.toSigRelativeString)
    info("Language:")
    encoding.encode(instProof).toSeq.map(_.toUntypedString(BabelSignature.defaultSignature)).sorted.foreach(info(_))

    // FIXME: still broken for uninterpreted sorts
    val grounding = Substitution(freeVariablesET(instProof).diff(freeVariables(inst)).map(v => v -> mkGroundTerm(v.ty)))
    grounding(instProof)
  }

}

class TreeGrammarInductionTactic(options: TreeGrammarProverOptions = TreeGrammarProverOptions())(implicit ctx: Context) extends Tactical1[Unit] {
  import gapt.proofs.gaptic._

  def copy(options: TreeGrammarProverOptions) = new TreeGrammarInductionTactic(options)

  def instanceNumber(n: Int) = copy(options.copy(instanceNumber = n))
  def instanceSize(from: Float, to: Float) = copy(options.copy(instanceSize = (from, to)))
  def instanceProver(prover: Prover) = copy(options.copy(instanceProver = prover))
  def smtSolver(prover: Prover) = copy(options.copy(smtSolver = prover))
  def smtEquationMode(mode: TreeGrammarProverOptions.SmtEquationMode) = copy(options.copy(smtEquationMode = mode))
  def quantTys(tys: TBase*) = copy(options.copy(quantTys = Some(tys)))
  def grammarWeighting(w: ProductionWeight) = copy(options.copy(grammarWeighting = w))
  def tautCheckNumber(n: Int) = copy(options.copy(tautCheckNumber = n))
  def tautCheckSize(from: Float, to: Float) = copy(options.copy(tautCheckSize = (from, to)))
  def canSolSize(from: Float, to: Float) = copy(options.copy(canSolSize = (from.toFloat, to.toFloat)))
  def canSolSize(size: Int) = copy(options.copy(canSolSize = (size.toFloat, size.toFloat)))
  def equationalTheory(equations: Formula*) = copy(options.copy(equationalTheory = equations))
  def maxsatSolver(solver: MaxSATSolver) = copy(options.copy(maxSATSolver = solver))
  def useInterpolation = copy(options.copy(bupSolver = InductionBupSolver.Interpolation))

  override def apply(goal: OpenAssumption): Tactic[Unit] = {
    implicit val ctx2: MutableContext = ctx.newMutable
    try replace(withSection { section =>
        val groundGoal = section.groundSequent(goal.conclusion)
        val viper = new TreeGrammarProver(ctx2, groundGoal, options)
        viper.solve()
      })
    catch {
      case t: TimeOutException     => throw t
      case t: InterruptedException => throw t
      case t: Throwable =>
        TacticFailure(this, ExceptionUtils.getStackTrace(t))
    }
  }

  override def toString = "treeGrammarInduction"
}
