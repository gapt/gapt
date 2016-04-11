package at.logic.gapt.proofs

import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic.tactics._
import at.logic.gapt.proofs.lk.{ LKProof, TheoryAxiom }

import scalaz._
import Scalaz._

/**
 * Foo
 */
package object gaptic {
  // LK Tactics

  /**
   * Applies the `LogicalAxiom` tactic to the current subgoal: A subgoal of the form `A, Γ :- Δ, A` will be closed.
   */
  def axiomLog = LogicalAxiomTactic

  /**
   * Applies the `TopAxiom` tactic to the current subgoal: A subgoal of the form `Γ :- Δ, ⊤` will be closed.
   */
  def axiomTop = TopAxiomTactic

  /**
   * Applies the `BottomAxiom` tactic to the current subgoal: A subgoal of the form `⊥, Γ :- Δ` will be closed.
   */
  def axiomBot = BottomAxiomTactic

  /**
   * Applies the `ReflexivityAxiom` tactic to the current subgoal: A subgoal of the form `Γ :- Δ, s = s` will be closed.
   */
  def axiomRefl = ReflexivityAxiomTactic

  /**
   * Synonym for [[axiomRefl]].
   */
  def refl = ReflexivityAxiomTactic

  /**
   * Attempts to apply the tactics `axiomTop`, `axiomBot`, `axiomRefl`, and `axiomLog`.
   */
  def trivial = axiomTop orElse axiomBot orElse axiomRefl orElse axiomLog

  /**
   * Applies the `NegLeft` tactic to the current subgoal: The goal
   *
   * `¬A, Γ :- Δ`
   *
   * is reduced to
   *
   * `Γ :- Δ, A`.
   * @param applyToLabel The label of the formula `¬A`.
   */
  def negL( applyToLabel: String ) = new NegLeftTactic( OnLabel( applyToLabel ) )

  /**
   * Applies the `NegLeft` tactic to the current subgoal: The goal
   *
   * `¬A, Γ :- Δ`
   *
   * is reduced to
   *
   * `Γ :- Δ, A`.
   *
   * This will only work if there is exactly one negated formula in the antecedent!
   */
  def negL = new NegLeftTactic()

  /**
   * Applies the `NegRight` tactic to the current subgoal: The goal
   *
   * `Γ :- Δ, ¬A`
   *
   * is reduced to
   *
   * `A, Γ :- Δ`.
   * @param applyToLabel The label of the formula `¬A`.
   */
  def negR( applyToLabel: String ) = new NegRightTactic( OnLabel( applyToLabel ) )

  /**
   * Applies the `NegRight` tactic to the current subgoal: The goal
   *
   * `Γ :- Δ, A`
   *
   * is reduced to
   *
   * `A, Γ :- Δ`.
   *
   * This will only work if there is exactly one negated formula in the succedent!
   */
  def negR = new NegRightTactic()

  /**
   * Applies the `AndLeft` tactic to the current subgoal: The goal
   *
   * `A ∧ B, Γ :- Δ`
   *
   * is reduced to
   *
   * `A, B, Γ :- Δ`.
   * @param applyToLabel The label of the formula `A ∧ B`.
   */
  def andL( applyToLabel: String ) = new AndLeftTactic( OnLabel( applyToLabel ) )

  /**
   * Applies the `AndLeft` tactic to the current subgoal: The goal
   *
   * `A ∧ B, Γ :- Δ`
   *
   * is reduced to
   *
   * `A, B, Γ :- Δ`.
   *
   * This will only work if there is exactly one conjunctive formula in the antecedent!
   */
  def andL = new AndLeftTactic()

  /**
   * Applies the `AndRight` tactic to the current subgoal: The goal
   *
   * `Γ :- Δ, A ∧ B`
   *
   * is reduced to
   *
   * `Γ :- Δ, A` and `Γ :- Δ, B`.
   * @param applyToLabel The label of the formula `A ∧ B`.
   */
  def andR( applyToLabel: String ) = new AndRightTactic( OnLabel( applyToLabel ) )

  /**
   * Applies the `AndRight` tactic to the current subgoal: The goal
   *
   * `Γ :- Δ, A ∧ B`
   *
   * is reduced to
   *
   * `Γ :- Δ, A` and `Γ :- Δ, B`.
   *
   * This will only work if there is exactly one conjunctive formula in the succedent!
   */
  def andR = new AndRightTactic()

  /**
   * Applies the `OrLeft` tactic to the current subgoal: The goal
   *
   * `A ∨ B, Γ :- Δ`
   *
   * is reduced to
   *
   * `A, Γ :- Δ` and `B, Γ :- Δ`.
   * @param applyToLabel The label of the formula `A ∨ B`.
   */
  def orL( applyToLabel: String ) = new OrLeftTactic( OnLabel( applyToLabel ) )

  /**
   * Applies the `OrLeft` tactic to the current subgoal: The goal
   *
   * `A ∨ B, Γ :- Δ`
   *
   * is reduced to
   *
   * `A, Γ :- Δ` and `B, Γ :- Δ`.
   *
   * This will only work if there is exactly one disjunctive formula in the antecedent!
   */
  def orL = new OrLeftTactic()

  /**
   * Applies the `OrRight` tactic to the current subgoal: The goal
   *
   * `Γ :- Δ, A ∨ B`
   *
   * is reduced to
   *
   * `Γ :- Δ, A, B`.
   * @param applyToLabel The label of the formula `A ∨ B`.
   */
  def orR( applyToLabel: String ) = new OrRightTactic( OnLabel( applyToLabel ) )

  /**
   * Applies the `OrRight` tactic to the current subgoal: The goal
   *
   * `Γ :- Δ, A ∨ B`
   *
   * is reduced to
   *
   * `Γ :- Δ, A, B`.
   *
   * This will only work if there is exactly one disjunctive formula in the succedent!
   */
  def orR = new OrRightTactic()

  /**
   * Applies the `ImpLeft` tactic to the current subgoal: The goal
   *
   * `A → B, Γ :- Δ`
   *
   * is reduced to
   *
   * `Γ :- Δ, A` and `B, Γ :- Δ`.
   * @param applyToLabel The label of the formula `A → B`.
   */
  def impL( applyToLabel: String ) = new ImpLeftTactic( OnLabel( applyToLabel ) )

  /**
   * Applies the `ImpLeft` tactic to the current subgoal: The goal
   *
   * `A → B, Γ :- Δ`
   *
   * is reduced to
   *
   * `Γ :- Δ, A` and `B, Γ :- Δ`.
   *
   * This will only work if there is exactly one implicative formula in the antecedent!
   */
  def impL = new ImpLeftTactic()

  /**
   * Applies the `ImpRight` tactic to the current subgoal: The goal
   *
   * `Γ :- Δ, A → B`
   *
   * is reduced to
   *
   * `A, Γ :- Δ, B`.
   * @param applyToLabel The label of the formula `A → B`.
   */
  def impR( applyToLabel: String ) = new ImpRightTactic( OnLabel( applyToLabel ) )

  /**
   * Applies the `ImpRight` tactic to the current subgoal: The goal
   *
   * `Γ :- Δ, A → B`
   *
   * is reduced to
   *
   * `A, Γ :- Δ, B`.
   *
   * This will only work if there is exactly one implicative formula in the succedent!
   */
  def impR = new ImpRightTactic()

  /**
   * Applies the `ExistsLeft` tactic to the current subgoal: The goal
   *
   * `∃x.A, Γ :- Δ`
   *
   * is reduced to
   *
   * `A[x\α], Γ :- Δ`.
   * @param applyToLabel The label of the formula `∃x.A`.
   * @param eigenVariable The variable `α`.
   */
  def exL( applyToLabel: String, eigenVariable: Var ) = new ExistsLeftTactic( OnLabel( applyToLabel ), Some( eigenVariable ) )

  /**
   * Applies the `ExistsLeft` tactic to the current subgoal: The goal
   *
   * `∃x.A, Γ :- Δ`
   *
   * is reduced to
   *
   * `A[x\α], Γ :- Δ`.
   *
   * This will only work if there is exactly one existential formula in the antecedent!
   * @param eigenVariable The variable `α`.
   */
  def exL( eigenVariable: Var ) = new ExistsLeftTactic( eigenVariable = Some( eigenVariable ) )

  /**
   * Applies the `ExistsLeft` tactic to the current subgoal: The goal
   *
   * `∃x.A, Γ :- Δ`
   *
   * is reduced to
   *
   * `A, Γ :- Δ`.
   * @param applyToLabel The label of the formula `∃x.A`.
   */
  def exL( applyToLabel: String ) = new ExistsLeftTactic( OnLabel( applyToLabel ) )

  /**
   * Applies the `ExistsLeft` tactic to the current subgoal: The goal
   *
   * `∃x.A, Γ :- Δ`
   *
   * is reduced to
   *
   * `A, Γ :- Δ`.
   *
   * This will only work if there is exactly one existential formula in the antecedent!
   */
  def exL = new ExistsLeftTactic()

  /**
   * Applies the `ExistsRight` tactic to the current subgoal: The goal
   *
   * `Γ :- Δ, ∃x,,1,,...∃x,,n,,.A`
   *
   * is reduced to
   *
   * `Γ :- Δ, ∃x,,1,,...∃x,,n,,.A, A[x,,1,,\t,,1,,,...,x,,n,,\t,,n,,]`.
   * @param applyToLabel The label of the formula `∃x,,1,,...∃x,,n,,.A`.
   * @param term The term `t,,1,,`.
   * @param terms The terms `t,,2,,,...,t,,n,,`.
   */
  def exR( applyToLabel: String, term: LambdaExpression, terms: LambdaExpression* ) = new ExistsRightTactic( OnLabel( applyToLabel ), term +: terms, instantiateOnce = false )

  /**
   * Applies the `ExistsRight` tactic to the current subgoal: The goal
   *
   * `Γ :- Δ, ∃x,,1,,...∃x,,n,,.A`
   *
   * is reduced to
   *
   * `Γ :- Δ, ∃x,,1,,...∃x,,n,,.A, A[x,,1,,\t,,1,,,...,x,,n,,\t,,n,,]`.
   *
   * This will only work if there is exactly one existential formula in the succedent!
   * @param term The term `t,,1,,`.
   * @param terms The terms `t,,2,,,...,t,,n,,`.
   */
  def exR( term: LambdaExpression, terms: LambdaExpression* ) = new ExistsRightTactic( UniqueFormula, term +: terms, instantiateOnce = false )

  /**
   * Applies the `ForallLeft` tactic to the current subgoal: The goal
   *
   * `∀x,,1,,,...,∀x,,n,,.A, Γ :- Δ`
   *
   * is reduced to
   *
   * `A[x,,1,,\t,,1,,,...,x,,n,,\t,,n,,], ∀x,,1,,,...,∀x,,n,,.A, Γ :- Δ`.
   * @param applyToLabel The label of the formula `∀x,,1,,,...,∀x,,n,,.A`.
   * @param term The term `t,,1,,`.
   * @param terms The terms `t,,2,,,...,t,,n,,`.
   */
  def allL( applyToLabel: String, term: LambdaExpression, terms: LambdaExpression* ) = new ForallLeftTactic( OnLabel( applyToLabel ), term +: terms, instantiateOnce = false )

  /**
   * Applies the `ForallLeft` tactic to the current subgoal: The goal
   *
   * `∀x,,1,,,...,∀x,,n,,.A, Γ :- Δ`
   *
   * is reduced to
   *
   * A[x,,1,,\t,,1,,,...,x,,n,,\t,,n,,], ∀x,,1,,,...,∀x,,n,,.A, Γ :- Δ.
   *
   * This will only work if there is exactly one universal formula in the antecedent!
   * @param term The term `t,,1,,`.
   * @param terms The terms `t,,2,,,...,t,,n,,`.
   */
  def allL( term: LambdaExpression, terms: LambdaExpression* ) = new ForallLeftTactic( UniqueFormula, term +: terms, instantiateOnce = false )

  /**
   * Applies the `ForallRight` tactic to the current subgoal: The goal
   *
   * `Γ :- Δ, ∀x.A`
   *
   * is reduced to
   *
   * `Γ :- Δ, A[x\α]`.
   * @param applyToLabel The label of the formula `∀x.A`.
   * @param eigenVariable The variable `α`.
   */
  def allR( applyToLabel: String, eigenVariable: Var ) = new ForallRightTactic( OnLabel( applyToLabel ), Some( eigenVariable ) )

  /**
   * Applies the `ForallRight` tactic to the current subgoal: The goal
   *
   * `Γ :- Δ, ∀x.A`
   *
   * is reduced to
   *
   * `Γ :- Δ, A[x\α]`.
   *
   * This will only work if there is exactly one universal formula in the succedent!
   * @param eigenVariable The variable `α`.
   */
  def allR( eigenVariable: Var ) = new ForallRightTactic( eigenVariable = Some( eigenVariable ) )

  /**
   * Applies the `ForallRight` tactic to the current subgoal: The goal
   *
   * `Γ :- Δ, ∀x.A`
   *
   * is reduced to
   *
   * `Γ :- Δ, A`.
   * @param applyToLabel The label of the formula `∀x.A`.
   */
  def allR( applyToLabel: String ) = new ForallRightTactic( OnLabel( applyToLabel ) )

  /**
   * Applies the `ForallRight` tactic to the current subgoal: The goal
   *
   * `Γ :- Δ, ∀x.A`
   *
   * is reduced to
   *
   * `Γ :- Δ, A`.
   *
   * This will only work if there is exactly one universal formula in the succedent!
   */
  def allR = new ForallRightTactic()

  /**
   * Applies the `Cut` tactic to the current subgoal: The goal
   *
   * `Γ :- Δ`
   *
   * is reduced to
   *
   * `Γ :- Δ, C` and `C, Γ :- Δ`.
   * @param label The label of `C`.
   * @param cutFormula The formula `C`.
   */
  def cut( label: String, cutFormula: HOLFormula ) = CutTactic( label, cutFormula )

  /**
   * Applies the `Equality` tactic to the current subgoal: Given an equation `s = t` and a formula `A`,
   * some occurrences of `s` in A are replaced by `t` or vice versa. The exact behavior can be controlled with
   * additional commands:
   *
   * - `fromLeftToRight`: Occurrences of `s` will be replaced by `t`.
   * - `fromRightToLeft`: Occurrences of `t` will be replaced by `s`.
   * - `yielding(f)`: The tactic will attempt to replace occurences in such a way that the end result is `f`.
   *
   * If neither `fromLeftToRight` nor `fromRightToLeft` is used, the direction of replacement needs to be unambiguous,
   * i.e. `s` and `t` may not both occur in `A`.
   * @param eq The label of `s = t`.
   * @param fm The label of `A`.
   */
  def eql( eq: String, fm: String ) = EqualityTactic( eq, fm )

  /**
   * Applies the `Induction` tactic to the current subgoal: The goal
   *
   * `Γ, :- Δ, ∀x.A`
   *
   * is reduced to `n` new subgoals, where `n` is the number of constructors of the type of `x`.
   *
   * This will only work if there is exactly one universal formula in the succedent!
   * @param ctx A [[at.logic.gapt.proofs.Context]]. It must contain an inductive definition of the type of `x`.
   */
  def induction( implicit ctx: Context ) = InductionTactic( UniqueFormula )

  /**
   * Applies the `Induction` tactic to the current subgoal: The goal
   *
   * `Γ, :- Δ, ∀x.A`
   *
   * is reduced to `n` new subgoals, where `n` is the number of constructors of the type of `x`.
   * @param label The label of the formula `∀x.A`.
   * @param ctx A [[at.logic.gapt.proofs.Context]]. It must contain an inductive definition of the type of `x`.
   */
  def induction( label: String )( implicit ctx: Context ) = InductionTactic( OnLabel( label ) )

  // Meta

  /**
   * Inserts an LKProof for the current subgoal.
   * @param proof The proof to be inserted. Its end-sequent must subsume the current goal.
   */
  def insert( proof: LKProof ) = InsertTactic( proof )

  /**
   *
   * @param label
   * @param proof
   * @return
   */
  def include( label: String, proof: LKProof ): Tactical[Unit] =
    for {
      goal <- currentGoal
      diff = proof.conclusion diff goal.conclusion
      cutFormula = diff.toDisjunction
      _ <- cut( label, cutFormula )
      _ <- insert( proof )
    } yield ()

  /**
   * Declares the current subgoal as a theory axiom, i.e. a sequent that is contained in the background theory. This
   * closes the goal.
   * @param ctx A [[at.logic.gapt.proofs.Context]]. The current subgoal must be contained in its background theory.
   */
  def theory( implicit ctx: Context ): Tactical[Unit] =
    for {
      goal <- currentGoal
      theoryAxiom <- ctx.theory( goal.conclusion collect { case a: HOLAtom => a } ).
        toTactical( "does not follow from theory", goal )
      _ <- insert( theoryAxiom )
    } yield ()

  /**
   * Repeats a tactical until it fails.
   * @param t A tactical.
   */
  def repeat[T]( t: Tactical[T] ) = RepeatTactic( t )

  /**
   * Leaves a hole in the current proof by inserting a dummy proof of the empty sequent.
   */
  @deprecated( "Proof not finished!", since = "the dawn of time" )
  def sorry = insert( TheoryAxiom( Clause() ) )

  /**
   * Tactic that immediately fails.
   */
  def fail = new Tactical[Nothing] {
    def apply( proofState: ProofState ): ValidationNel[TacticalFailure, ( Nothing, ProofState )] =
      TacticalFailure( this, None, "explicit fail" ).failureNel
    override def toString = "fail"
  }

  // Complex

  /**
   * Decomposes the current subgoal by applying all "simple" rules as often as possible. These rules are:
   * - `¬:l` and `¬:r`
   * - `∧:l`
   * - `∨:r`
   * - `→:r`
   * - `∃:l`
   * - `∀:r`
   */
  def decompose = DecomposeTactic

  def destruct( label: String ) = DestructTactic( label )

  def chain( h: String ) = ChainTactic( h )

  /**
   * Calls the builtin tableau prover on the current subgoal. If the goal is a tautology, a proof will automatically be
   * found and inserted.
   */
  def prop = PropTactic

  /**
   * Calls `prover9` on the current subgoal.
   */
  def prover9 = Prover9Tactic

  /**
   * Calls `escargot` on the current subgoal.
   */
  def escargot = EscargotTactic

  /**
   * Lets you "forget" a sequence of formulas, i.e. the tactics version of the weakening rule.
   * The formulas with labels `L,,1,,,...,L,,n,,` will be removed from the current goal.
   * @param l The label `L,,1,,`.
   * @param ls The labels `L,,2,,`,...,`,,Ln,,`.
   *
   */
  def forget( l: String, ls: String* ): Tactical[Unit] =
    l +: ls map { label => WeakeningLeftTactic( label ) orElse WeakeningRightTactic( label ) } reduce[Tactical[Unit]] ( _ andThen _ )

  /**
    * Moves the specified goal to the front of the goal list.
    * @param indexOfSubGoal The index of the goal.
    */
  def focus( indexOfSubGoal: Int ) = new FocusTactical( Left( indexOfSubGoal ) )

  /**
    * Moves the specified goal to the front of the goal list.
    * @param indexOfSubGoal The index of the goal.
    */
  def focus( indexOfSubGoal: OpenAssumptionIndex ) = new FocusTactical( Right( indexOfSubGoal ) )

  /**
    * Changes the provided label. Syntax:
    *
    * {{{
    *   renameLabel("foo") to "bar"
    * }}}
    * @param oldLabel The label to be renamed.
    */
  def renameLabel( oldLabel: String ) = RenameTactic( oldLabel, oldLabel )

  def rewrite = RewriteTactic( equations = Seq(), target = None, once = true )

  /**
    * Replaces a defined constant with its definition. Syntax:
    *
    * {{{
    *   unfold("def1", "def2",...,"defn") in ("label1", "label2",...,"labelk")
    * }}}
    *
    * NB: This will only replace the first definition it finds in each supplied formula. If you want to unfold all definitions,
    * use `repeat`.
    * @param definition The definition `def1`.
    * @param definitions The definitions `def2`,...,`defn`.
    * @param ctx A [[at.logic.gapt.proofs.Context]]. The definitions you want to unfold need to be present in `ctx`.
    */
  def unfold( definition: String, definitions: String* )( implicit ctx: Context ) =
    UnfoldTacticHelper( definition, definitions )

  /**
    * Does nothing.
    */
  def skip = SkipTactical

  /**
    * Retrieves the current subgoal.
    */
  def currentGoal: Tactic[OpenAssumption] = new Tactic[OpenAssumption] {
    def apply( goal: OpenAssumption ) = ( goal -> goal ).success
  }

  /**
    * Implementation of the [[scalaz.Monad]] typeclass for Tacticals.
    */
  implicit object TacticalMonad extends Monad[Tactical] {
    def point[A]( a: => A ): Tactical[A] = new Tactical[A] {
      def apply( proofState: ProofState ) = ( a -> proofState ).success
    }

    def bind[A, B]( fa: Tactical[A] )( f: A => Tactical[B] ): Tactical[B] =
      fa flatMap f
  }

  implicit class TacticalOptionOps[T]( option: Option[T] ) {
    def toTactical( errorMsg: String ): Tactical[T] = toTactical( errorMsg, None )
    def toTactical( errorMsg: String, goal: OpenAssumption ): Tactical[T] = toTactical( errorMsg, Some( goal ) )
    def toTactical( errorMsg: String, goal: Option[OpenAssumption] ): Tactical[T] = new Tactical[T] {
      override def apply( proofState: ProofState ) =
        option match {
          case None          => TacticalFailure( this, goal, errorMsg ).failureNel
          case Some( value ) => ( value -> proofState ).success
        }

      override def toString = s"$option.toTactical"
    }
  }
}
