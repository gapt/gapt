package gapt.proofs.gaptic

import gapt.expr._
import gapt.proofs.{HOLSequent, Sequent, SequentConnector, SequentIndex}
import gapt.proofs.lk._
import gapt.formats.babel.BabelSignature
import gapt.utils.{Logger, NameGenerator}
import cats.syntax.all._
import cats.instances.all._
import gapt.expr.formula.Formula
import gapt.proofs.lk.rules.InitialSequent
import gapt.proofs.lk.rules.macros.WeakeningContractionMacroRule

object guessLabels {
  def suggestLabel(formula: Formula, idx: SequentIndex, nameGen: NameGenerator): String =
    formula match {
      case Const(name, _, _) => nameGen.fresh(name)
      case _ if idx.isSuc    => nameGen.fresh("g")
      case _ if idx.isAnt    => nameGen.freshWithIndex("h")
    }

  def apply(sequent: HOLSequent): Sequent[(String, Formula)] = {
    val nameGen = new NameGenerator(Set())
    for ((f, i) <- sequent.zipWithIndex)
      yield suggestLabel(f, i, nameGen) -> f
  }
}

object ProofState {
  def apply(initialGoal: OpenAssumption): ProofState =
    ProofState(initialGoal, List(initialGoal), Map())
  def apply(initialGoal: Sequent[(String, Formula)]): ProofState =
    ProofState(OpenAssumption(initialGoal))
  def apply(initialGoal: HOLSequent)(implicit dummyImplicit: DummyImplicit): ProofState =
    apply(guessLabels(initialGoal))
  def apply(initialGoal: Formula): ProofState =
    apply(Sequent() :+ initialGoal)
}
case class ProofState private (
    initialGoal: OpenAssumption,
    subGoals: List[OpenAssumption],
    finishedSubGoals: Map[OpenAssumptionIndex, LKProof]
) {

  def isFinished: Boolean = subGoals.isEmpty

  def currentSubGoalOption: Option[OpenAssumption] = subGoals.headOption

  def setSubGoals(newSubGoals: List[OpenAssumption]): ProofState =
    copy(subGoals = newSubGoals)

  def focus(index: OpenAssumptionIndex): ProofState = {
    val (focused, rest) = subGoals.partition(_.index == index)
    setSubGoals(focused ++ rest)
  }

  def replace(index: OpenAssumptionIndex, proofSegment: LKProof): ProofState = {
    val subGoal = subGoals.find(_.index == index).getOrElse(
      throw new IllegalArgumentException(s"Cannot replace non-existing open subgoal: $index")
    )
    require(
      proofSegment.conclusion isSubsetOf subGoal.conclusion,
      s"Conclusion of proof segment is not a subset of subgoal:\n${proofSegment.conclusion}\nis not a subset of\n${subGoal.conclusion}\n"
        + s"Extra formulas:\n${proofSegment.conclusion.distinct.diff(subGoal.conclusion)}"
    )

    if (subGoal == proofSegment) return this

    val newOpenAssumptions = proofSegment.treeLike.postOrder.collect { case oa: OpenAssumption => oa }.distinct

    val subGoals_ = subGoals.filter(_.index != index).diff(newOpenAssumptions)

    for ((idx, oas) <- newOpenAssumptions.groupBy(_.index))
      require(oas.size == 1, s"Different new open assumptions with same index:\n${oas.mkString("\n")}")
    require(
      newOpenAssumptions intersect subGoals_ isEmpty,
      s"New open assumption contains already open subgoal"
    )
    require(
      newOpenAssumptions.map(_.index).toSet intersect finishedSubGoals.keySet isEmpty,
      s"New open assumption contains already finished subgoal"
    )

    copy(
      subGoals = newOpenAssumptions.toList ++ subGoals_,
      finishedSubGoals = finishedSubGoals + (index -> proofSegment)
    )
  }

  def replace(proofSegment: LKProof): ProofState = replace(subGoals.head.index, proofSegment)

  class ProofSegmentInsertionVisitor(failOnMissingSubgoal: Boolean) extends LKVisitor[Unit] {
    override def visitOpenAssumption(p: OpenAssumption, dummy: Unit): (LKProof, SequentConnector) = {
      finishedSubGoals.get(p.index) match {
        case Some(segment) =>
          val subProof = recurse(segment, ())._1
          require(subProof.conclusion multiSetEquals segment.conclusion)
          val segment_ = WeakeningContractionMacroRule(subProof, p.conclusion)
          require(segment_.conclusion multiSetEquals p.conclusion)
          (segment_, SequentConnector.guessInjection(fromLower = p.conclusion, toUpper = segment_.conclusion).inv)
        case None =>
          if (failOnMissingSubgoal)
            throw new IllegalArgumentException(s"Subgoal still open: $p")
          else
            super.visitOpenAssumption(p, dummy)
      }
    }
  }

  def partialProof: LKProof = new ProofSegmentInsertionVisitor(failOnMissingSubgoal = false).apply(initialGoal, ())
  def result: LKProof = new ProofSegmentInsertionVisitor(failOnMissingSubgoal = true).apply(initialGoal, ())

  override def toString = toSigRelativeString
  def toSigRelativeString(implicit sig: BabelSignature) =
    subGoals.map { _.toPrettyString }.mkString("\n")

  def +[A](tactical: Tactic[A])(implicit sig: BabelSignature): ProofState =
    tactical(this) match {
      case Right((_, newState)) => newState
      case Left(error) =>
        throw new TacticFailureException(s"$this\n${error.toSigRelativeString}")
    }
}

/**
 * The globally unique index of an open assumption in a proof state.
 */
class OpenAssumptionIndex {
  override def toString = Integer toHexString hashCode() take 3
}

/**
 * Defines the case class open assumption which considers an arbitrary labelled sequence an axiom.
 */
case class OpenAssumption(
    labelledSequent: Sequent[(String, Formula)],
    index: OpenAssumptionIndex = new OpenAssumptionIndex
) extends InitialSequent {
  override def name = "ass"

  def labels = labelledSequent.map(_._1)
  override def conclusion = labelledSequent map { labelledFormula => labelledFormula._2 }

  def apply(label: String): Formula = labelledSequent.elements.find(_._1 == label).get._2

  def toPrettyString(implicit sig: BabelSignature) = {
    val builder = new StringBuilder
    for ((l, f) <- labelledSequent.antecedent) builder append s"$l: ${f.toSigRelativeString}\n"
    builder append ":-\n"
    for ((l, f) <- labelledSequent.succedent) builder append s"$l: ${f.toSigRelativeString}\n"
    builder.toString
  }
}

/**
 * Class that describes how a tactic should be applied: to a label, to the unique fitting formula, or to any fitting formula.
 */
sealed abstract class TacticApplyMode {
  def forall(p: String => Boolean): Boolean
}

/**
 * Apply a tactic to a specific label.
 *
 * @param label The label that the tactic should be applied to.
 */
case class OnLabel(label: String) extends TacticApplyMode {
  def forall(p: String => Boolean): Boolean = p(label)
}

/**
 * Apply a tactic only if there is exactly one formula that fits.
 */
case object UniqueFormula extends TacticApplyMode {
  def forall(p: String => Boolean): Boolean = true
}

/**
 * Apply a tactic if there is a formula that fits.
 */
case object AnyFormula extends TacticApplyMode {
  def forall(p: String => Boolean): Boolean = true
}

case class TacticFailure(tactic: Tactic[_], state: Option[ProofState], message: String) {
  def defaultState(proofState: ProofState): TacticFailure =
    copy(state = Some(state.getOrElse(proofState)))

  override def toString = toSigRelativeString
  def toSigRelativeString(implicit sig: BabelSignature) =
    s"$tactic:\n$message:\n\n${state.map(_.toSigRelativeString).getOrElse("")}"
  def reassignTactic(newTactical: Tactic[_]) =
    TacticFailure(newTactical, state, s"$tactic:\n$message")
}
object TacticFailure {
  def apply(tactical: Tactic[_], state: ProofState, message: String): TacticFailure =
    TacticFailure(tactical, Some(state), message)
  def apply(tactical: Tactic[_], message: String): TacticFailure =
    TacticFailure(tactical, None, message)
}

trait Tactic[+T] { self =>
  def apply(proofState: ProofState): Either[TacticFailure, (T, ProofState)]

  /**
   * Returns result of first tactical, if there is any,
   * else it returns the result of the second tactical,
   * with the possibility of no result from either.
   *
   * @param t2
   * @return
   */
  def orElse[S >: T](t2: => Tactic[S]): Tactic[S] = {
    val t1 = this

    new Tactic[S] {
      override def apply(proofState: ProofState) = {
        t1(proofState).orElse(t2(proofState))
      }
      override def toString = s"$t1 orElse $t2"
    }
  }

  def andThen[S](t2: => Tactic[S]): Tactic[S] = new Tactic[S] {
    def apply(proofState: ProofState) = self(proofState) flatMap { x => t2(x._2) }
    override def toString = s"$self andThen $t2"
  }

  def map[S](f: T => S)(implicit file: sourcecode.File, line: sourcecode.Line): Tactic[S] = new Tactic[S] {
    def apply(proofState: ProofState) = self(proofState) map { x => f(x._1) -> x._2 }
    override def toString = s"$self.map(<${file.value}:${line.value}>)"
  }

  def flatMap[S](f: T => Tactic[S])(implicit file: sourcecode.File, line: sourcecode.Line): Tactic[S] = new Tactic[S] {
    def apply(proofState: ProofState) = self(proofState) flatMap { x => f(x._1)(x._2) }
    override def toString = s"$self.flatMap(<${file.value}:${line.value}>)"
  }

  private def applyToSubgoal(proofState: ProofState, subGoal: OpenAssumptionIndex, tacticToBlame: Tactic[_] = this): Either[TacticFailure, (T, ProofState)] =
    proofState.subGoals.indexWhere(_.index == subGoal) match {
      case -1 => Left(TacticFailure(tacticToBlame, proofState, "Did not find specified subgoal"))
      case i =>
        val focused = proofState.subGoals(i)
        self(proofState.setSubGoals(List(focused))).flatMap {
          case (res, newState) =>
            Right((res, newState.setSubGoals(proofState.subGoals.take(i) ++ newState.subGoals ++ proofState.subGoals.drop(i + 1))))
        }
    }

  def onCurrentSubGoal: Tactic[T] = new Tactic[T] {
    override def apply(proofState: ProofState) = proofState.currentSubGoalOption match {
      case Some(goal) =>
        self.applyToSubgoal(proofState, goal.index, this)
      case None =>
        Left(TacticFailure(this, proofState, "No open subgoal"))
    }
    override def toString = s"$self.onCurrentSubGoal"
  }

  def focused: Tactic[T] = new Tactic[T] {
    override def apply(proofState: ProofState) = {
      val focusedGoal = proofState.currentSubGoalOption.toList
      self(proofState.setSubGoals(focusedGoal)).flatMap {
        case (res, newState) if newState.subGoals.isEmpty =>
          Right((res, newState.setSubGoals(proofState.subGoals diff focusedGoal)))
        case (res, newState) =>
          Left(TacticFailure(this, newState, "focused goal not solved"))
      }
    }
    override def toString = s"$self.focused"
  }

  def onAllSubGoals: Tactic[Unit] = new Tactic[Unit] {
    override def apply(proofState: ProofState): Either[TacticFailure, (Unit, ProofState)] =
      proofState.subGoals.foldLeft[Either[TacticFailure, ProofState]](Right(proofState))((proofState_, subGoal) =>
        proofState_.flatMap(self.applyToSubgoal(_, subGoal.index, this)).map(_._2)
      ).map(() -> _)

    override def toString = s"$self.onAllSubGoals"
  }

  def onAll[S](t2: => Tactic[S]): Tactic[Unit] =
    flatMap(_ => t2.onAllSubGoals).onCurrentSubGoal.aka(s"$this.onAll($t2)")

  def aka(newName: => String): Tactic[T] = new Tactic[T] {
    def apply(proofState: ProofState) = self(proofState)
    override def toString = newName
  }

  def cut(errorMessage: String): Tactic[T] = new Tactic[T] {
    def apply(proofState: ProofState) =
      self(proofState).leftMap(_ => TacticFailure(self, proofState, errorMessage))
    override def toString = self.toString
  }

  def verbose: Tactic[T] = new Tactic[T] {
    override def apply(proofState: ProofState) =
      gapt.utils.verbose { self(proofState) }

    override def toString: String = s"${self.toString}.verbose"
  }
  def verboseOnly(loggers: Logger*): Tactic[T] = new Tactic[T] {
    override def apply(proofState: ProofState) =
      gapt.utils.verbose.only(loggers: _*) { self(proofState) }

    override def toString: String = s"${self.toString}.verboseOnly(${loggers.mkString(",")})"
  }

  def quiet: Tactic[T] = new Tactic[T] {
    override def apply(proofState: ProofState) =
      gapt.utils.quiet { self(proofState) }

    override def toString: String = s"${self.toString}.quiet"
  }
  def quietOnly(loggers: Logger*): Tactic[T] = new Tactic[T] {
    override def apply(proofState: ProofState) =
      gapt.utils.quiet.only(loggers: _*) { self(proofState) }

    override def toString: String = s"${self.toString}.quietOnly(${loggers.mkString(",")})"
  }
}
object Tactic {
  def apply[T](tactic: Tactic[T])(implicit name: sourcecode.Name, args: sourcecode.Args): Tactic[T] =
    new Tactic[T] {
      def apply(proofState: ProofState) = tactic(proofState).leftMap(_.reassignTactic(this))
      override def toString =
        if (args.value.isEmpty) name.value
        else s"${name.value}(${args.value.flatten.map(_.value).mkString(", ")})"
    }

  def sequence[T](tacticals: Seq[Tactic[T]]): Tactic[List[T]] = {
    tacticals.toList.sequence.aka(s"sequence(${tacticals.mkString(", ")})")
  }

  def sequence[T](tacticals: Sequent[Tactic[T]]): Tactic[Sequent[T]] =
    sequence(tacticals.elements).map(resultElements =>
      Sequent(
        resultElements.take(tacticals.antecedent.size),
        resultElements.drop(tacticals.antecedent.size)
      )
    ).aka(s"sequence($tacticals)")

  def guard(cond: => Boolean, message: => String)(implicit args: sourcecode.Args): Tactic[Unit] =
    new Tactic[Unit] {
      def apply(proofState: ProofState): Either[TacticFailure, (Unit, ProofState)] =
        if (cond) Right((), proofState)
        else Left(TacticFailure(this, proofState, message))
      override def toString = s"guard(${args.value.head.head})"
    }

  def pure[T](t: T): Tactic[T] = s => Right(t -> s)

  implicit def fromFailure(failure: TacticFailure): Tactic[Nothing] =
    _ => Left(failure)
}

trait Tactical[+T] extends Tactic[T] { self =>
  protected def apply: Tactic[T]

  override def apply(proofState: ProofState): Either[TacticFailure, (T, ProofState)] =
    apply.apply(proofState)
}

trait Tactical1[+T] extends Tactic[T] { self =>
  protected def apply(goal: OpenAssumption): Tactic[T]

  override def apply(proofState: ProofState): Either[TacticFailure, (T, ProofState)] =
    proofState.currentSubGoalOption match {
      case None       => Left(TacticFailure(this, proofState, "no open subgoal"))
      case Some(goal) => apply(goal).apply(proofState)
    }

  protected def replace(proof: LKProof): Tactic[Unit] =
    proofState => Right(() -> proofState.replace(proof))

  protected def findFormula(goal: OpenAssumption, mode: TacticApplyMode): FindFormula =
    new FindFormula(goal, mode)
  protected class FindFormula(goal: OpenAssumption, mode: TacticApplyMode) {
    type Val = (String, Formula, SequentIndex)

    def withFilter(pred: Val => Boolean): Tactic[Val] =
      goal.labelledSequent.zipWithIndex.elements.collect {
        case ((l, f), i) if mode.forall { _ == l } && pred(l, f, i) => (l, f, i)
      } match {
        case Seq(f) => Tactic.pure(f)
        case Seq(someFormula, _*) =>
          mode match {
            case AnyFormula => Tactic.pure(someFormula)
            case _          => TacticFailure(self, s"Formula could not be uniquely determined.")
          }
        case _ =>
          mode match {
            case OnLabel(l) => TacticFailure(self, s"Label $l not found.")
            case _          => TacticFailure(self, s"No matching formula found.")
          }
      }

    def flatMap[U](func: Val => Tactic[U]): Tactic[U] =
      withFilter(_ => true).flatMap(func)
  }
}

/**
 * Trait for tactics that create two new subgoals. Provides the `left` and `right` methods.
 */
trait BinaryTactic[+T] extends Tactic[T] {

  /**
   * Synonym for `andThen`.
   */
  def left(that: Tactic[Unit]): Tactic[Unit] = this andThen that.focused

  /**
   * Creates a new Tactical by first applying `this` to the current subgoal and then `that` to the new right subgoal.
   * @param that A Tactical.
   */
  def right(that: Tactic[Unit]): Tactic[Unit] = this andThen focus(1) andThen that.focused
}

/**
 * Object that wraps helper function to generate new label from an existing one
 */
object NewLabels {

  /**
   * Actual helper function for a fresh variable.
   *
   * @param sequent
   * @param fromLabel
   * @return
   */
  def apply(sequent: Sequent[(String, Formula)], fromLabel: String): LazyList[String] = {
    val regex = f"$fromLabel%s_([0-9]+)".r

    // Get integer subscripts (i.e 1, 2, 3 for x_1, x_2, x_3)
    val usedVariableSubscripts = {
      for ((label, _) <- sequent.elements; m <- regex findFirstMatchIn label)
        yield Integer parseInt (m group 1)
    }.toSet

    for (i <- LazyList from 0 if !usedVariableSubscripts(i)) yield f"$fromLabel%s_$i%d"
  }
}

object NewLabel {
  def apply(sequent: Sequent[(String, Formula)], fromLabel: String): String =
    NewLabels(sequent, fromLabel).head
}
