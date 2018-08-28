package gapt.proofs.gaptic

import gapt.expr._
import gapt.formats.babel.BabelSignature
import gapt.proofs._
import gapt.proofs.context
import gapt.proofs.context.Context
import gapt.proofs.context.MutableContext
import gapt.proofs.gaptic.tactics._
import gapt.proofs.lk._
import gapt.provers.Prover
import gapt.provers.escargot.Escargot
import gapt.provers.prover9.Prover9
import gapt.provers.simp.SimpTactic
import gapt.provers.viper.aip.axioms.GeneralInductionAxioms
import gapt.provers.viper.aip.axioms.StandardInductionAxioms
import gapt.provers.viper.grammars.TreeGrammarInductionTactic

/**
 * Predefined tactics in gaptic.
 */
object TacticCommands extends TacticCommands

trait TacticCommands {
  // LK Tactics

  /**
   * Applies the `LogicalAxiom` tactic to the current subgoal: A subgoal of the form `A, Γ :- Δ, A` will be closed.
   */
  def ref( proofName: String )( implicit ctx: Context ) = ProofLinkTactic( proofName )( ctx )

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
  def trivial: Tactic[Unit] = Tactic { axiomTop orElse axiomBot orElse axiomRefl orElse axiomLog }.
    cut( "Not a valid initial sequent" )

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
  def negL( applyToLabel: String ) = NegLeftTactic( OnLabel( applyToLabel ) )

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
  def negL = NegLeftTactic()

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
  def negR( applyToLabel: String ) = NegRightTactic( OnLabel( applyToLabel ) )

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
  def negR = NegRightTactic()

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
  def andL( applyToLabel: String ) = AndLeftTactic( OnLabel( applyToLabel ) )

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
  def andL = AndLeftTactic()

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
  def andR( applyToLabel: String ) = AndRightTactic( OnLabel( applyToLabel ) )

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
  def andR = AndRightTactic()

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
  def orL( applyToLabel: String ) = OrLeftTactic( OnLabel( applyToLabel ) )

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
  def orL = OrLeftTactic()

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
  def orR( applyToLabel: String ) = OrRightTactic( OnLabel( applyToLabel ) )

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
  def orR = OrRightTactic()

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
  def impL( applyToLabel: String ) = ImpLeftTactic( OnLabel( applyToLabel ) )

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
  def impL = ImpLeftTactic()

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
  def impR( applyToLabel: String ) = ImpRightTactic( OnLabel( applyToLabel ) )

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
  def impR = ImpRightTactic()

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
  def exL( applyToLabel: String, eigenVariable: Var ) = ExistsLeftTactic( OnLabel( applyToLabel ), Some( eigenVariable ) )

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
  def exL( eigenVariable: Var ) = ExistsLeftTactic( eigenVariable = Some( eigenVariable ) )

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
  def exL( applyToLabel: String ) = ExistsLeftTactic( OnLabel( applyToLabel ) )

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
  def exL = ExistsLeftTactic()

  /**
   * Applies the `ExistsRight` tactic to the current subgoal: The goal
   *
   * `Γ :- Δ, ∃x,,1,,...∃x,,n,,.A`
   *
   * is reduced to
   *
   * `Γ :- Δ, ∃x,,1,,...∃x,,n,,.A, A[x,,1,,\t,,1,,,...,x,,n,,\t,,n,,]`.
   * @param applyToLabel The label of the formula `∃x,,1,,...∃x,,n,,.A`.
   * @param terms The terms `t,,1,,,...,t,,n,,`.
   */
  def exR( applyToLabel: String, terms: Expr* ) = ExistsRightTactic( OnLabel( applyToLabel ), terms, instantiateOnce = false )

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
   * @param terms The terms `t,,1,,,...,t,,n,,`.
   */
  def exR( terms: Expr* ) = ExistsRightTactic( UniqueFormula, terms, instantiateOnce = false )

  /**
   * Applies the `ForallLeft` tactic to the current subgoal: The goal
   *
   * `∀x,,1,,,...,∀x,,n,,.A, Γ :- Δ`
   *
   * is reduced to
   *
   * `A[x,,1,,\t,,1,,,...,x,,n,,\t,,n,,], ∀x,,1,,,...,∀x,,n,,.A, Γ :- Δ`.
   * @param applyToLabel The label of the formula `∀x,,1,,,...,∀x,,n,,.A`.
   * @param terms The terms `t,,1,,,...,t,,n,,`.
   */
  def allL( applyToLabel: String, terms: Expr* ) = ForallLeftTactic( OnLabel( applyToLabel ), terms, instantiateOnce = false )

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
   * @param terms The terms `t,,1,,,...,t,,n,,`.
   */
  def allL( terms: Expr* ) = ForallLeftTactic( UniqueFormula, terms, instantiateOnce = false )

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
  def allR( applyToLabel: String, eigenVariable: Var ) = ForallRightTactic( OnLabel( applyToLabel ), Some( eigenVariable ) )

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
  def allR( eigenVariable: Var ) = ForallRightTactic( eigenVariable = Some( eigenVariable ) )

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
  def allR( applyToLabel: String ) = ForallRightTactic( OnLabel( applyToLabel ) )

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
  def allR = ForallRightTactic()

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
  def cut( label: String, cutFormula: Formula ) = CutTactic( label, cutFormula )

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
   *
   * @param ctx A [[Context]]. It must contain an inductive definition of the type of `x`.
   */
  def induction( on: Var )( implicit ctx: Context ) = InductionTactic( UniqueFormula, on )

  /**
   * Applies the `Induction` tactic to the current subgoal: The goal
   *
   * `Γ, :- Δ, ∀x.A`
   *
   * is reduced to `n` new subgoals, where `n` is the number of constructors of the type of `x`.
   *
   * @param label The label of the formula `∀x.A`.
   * @param ctx   A [[context.Context]]. It must contain an inductive definition of the type of `x`.
   */
  def induction( on: Var, label: String )( implicit ctx: Context ) = InductionTactic( OnLabel( label ), on )

  // Meta

  /**
   * Inserts an LKProof for the current subgoal.
   * @param proof The proof to be inserted. Its end-sequent must subsume the current goal.
   */
  def insert( proof: LKProof ) = InsertTactic( proof )

  /**
   * Uses an LKProof as a lemma.
   *
   * If `proof` ends in `Γ :- φ`, then the current goal
   *
   * `Γ, Π :- Λ`
   *
   * is reduced to
   *
   * `Γ, Π, φ :- Λ`
   *
   * @param proof The proof to insert as a lemma by a cut.
   * @param label the label for φ in the subgoal
   */
  def include( label: String, proof: LKProof ): Tactic[Unit] = Tactic {
    for {
      goal <- currentGoal
      diff = proof.conclusion diff goal.conclusion
      cutFormula = diff.toDisjunction
      _ <- cut( label, cutFormula )
      _ <- insert( proof )
    } yield ()
  }

  def include( names: Expr* )( implicit ctx: Context ): Tactic[Unit] = Tactic(
    Tactic.sequence( for ( l @ Apps( Const( n, _, _ ), _ ) <- names ) yield include( n, ProofLink( l ) ) )
      andThen TacticMonad.pure( () ) )

  def include( labels: String* )( implicit ctx: Context, dummyImplicit: DummyImplicit ): Tactic[Unit] =
    Tactic( include( labels.map( ProofLink( _ ).referencedProof ): _* ) )

  /**
   * Solves the current subgoal as a first-order consequence of the background theory. This
   * closes the goal.
   *
   * @param ctx A [[context.Context]]. The current subgoal must be contained in its background theory.
   */
  def foTheory( implicit ctx: Context ): Tactic[Unit] = Tactic {
    for {
      goal <- currentGoal
      theoryAxiom <- FOTheoryMacroRule.option( goal.conclusion collect { case a: Atom => a } ).
        toTactic( "does not follow from theory" )
      _ <- insert( theoryAxiom )
    } yield ()
  }

  /**
   * Declares the current subgoal as a theory axiom, i.e. a sequent that is contained in the background theory. This
   * closes the goal.
   *
   * @param ctx A [[context.Context]]. The current subgoal must be contained in its background theory.
   */
  def theory( implicit ctx: Context ): Tactic[Unit] = Tactic {
    for {
      goal <- currentGoal
      proofLinkName <- ctx.get[Context.ProofNames].find( goal.conclusion ).
        toTactic( "does not follow from theory" )
      _ <- insert( ProofLink( proofLinkName ) )
    } yield ()
  }

  /**
   * Repeats a tactical until it fails.
   * @param t A tactical.
   */
  def repeat[T]( t: Tactic[T] ) = RepeatTactic( t )

  /**
   * Leaves a hole in the current proof by inserting a dummy proof of the empty sequent.
   */
  @deprecated( "Proof not finished!", since = "the dawn of time" )
  def sorry: Tactic[Unit] = Tactic {
    for {
      goal <- currentGoal
      _ <- insert( ProofLink( foc"sorry", goal.conclusion ) )
    } yield ()
  }

  /**
   * Tactic that immediately fails.
   */
  def fail = new Tactic[Nothing] {
    def apply( proofState: ProofState ) = Left( TacticFailure( this, Some( proofState ), "explicit fail" ) )
    override def toString = "fail"
  }

  // Complex

  /**
   * Decomposes the current subgoal by applying all "simple" rules as often as possible. These rules are:
   * - `¬:l` and `¬:r`
   * - `∧:l`
   * - `∨:r`
   * - `→:r`
   * - `∀:r`
   * - `∃:l`
   */
  def decompose: Tactic[Unit] = Tactic {
    repeat {
      NegLeftTactic( AnyFormula ) orElse NegRightTactic( AnyFormula ) orElse
        AndLeftTactic( AnyFormula ) orElse OrRightTactic( AnyFormula ) orElse ImpRightTactic( AnyFormula ) orElse
        ForallRightTactic( AnyFormula ) orElse ExistsLeftTactic( AnyFormula )
    }
  }

  def destruct( label: String ): Tactic[Any] = Tactic {
    allR( label ) orElse exL( label ) orElse
      andL( label ) orElse andR( label ) orElse
      orL( label ) orElse orR( label ) orElse
      impL( label ) orElse impR( label ) orElse
      negL( label ) orElse negR( label )
  }.cut( s"Cannot destruct $label" )

  def chain( h: String ) = ChainTactic( h )

  /**
   * Calls the builtin tableau prover on the current subgoal. If the goal is a tautology, a proof will automatically be
   * found and inserted.
   */
  def prop: Tactic[Unit] = PropTactic
  def quasiprop: Tactic[Unit] = QuasiPropTactic

  def resolutionProver( prover: Prover )( implicit ctx: MutableContext ): ResolutionProverTactic =
    ResolutionProverTactic( prover )

  /**
   * Calls `prover9` on the current subgoal.
   */
  def prover9( implicit ctx: MutableContext ): ResolutionProverTactic = resolutionProver( Prover9 )

  /**
   * Calls `escargot` on the current subgoal.
   */
  def escargot( implicit ctx: MutableContext ): ResolutionProverTactic = resolutionProver( Escargot )

  /**
   * Lets you "forget" a sequence of formulas, i.e. the tactics version of the weakening rule.
   * The formulas with labels `L,,1,,,...,L,,n,,` will be removed from the current goal.
   * @param ls The labels `L,,1,,`,...,`,,Ln,,`.
   *
   */
  def forget( ls: String* ): Tactic[Unit] =
    Tactic( forget( ( l, _ ) => ls.contains( l ) ) )

  def forget( pred: ( String, Formula ) => Boolean ): Tactic[Unit] = Tactic {
    for {
      goal <- currentGoal
      _ <- insert( OpenAssumption( goal.labelledSequent.filterNot( lf => pred( lf._1, lf._2 ) ) ) )
    } yield ()
  }

  /**
   * Moves the specified goal to the front of the goal list.
   * @param indexOfSubGoal The index of the goal.
   */
  def focus( indexOfSubGoal: Int ) = FocusTactic( Left( indexOfSubGoal ) )

  /**
   * Moves the specified goal to the front of the goal list.
   * @param indexOfSubGoal The index of the goal.
   */
  def focus( indexOfSubGoal: OpenAssumptionIndex ) = FocusTactic( Right( indexOfSubGoal ) )

  /**
   * Changes the provided label. Syntax:
   *
   * {{{
   *   renameLabel("foo") to "bar"
   * }}}
   * @param oldLabel The label to be renamed.
   */
  def renameLabel( oldLabel: String ) = RenameTactic( oldLabel, oldLabel )

  /**
   * Rewrites the formula specified by target using (possibly universally quantified) equations.
   *
   * {{{
   *   rewrite.many ltr "equation1" in "target"
   *   rewrite.many ltr ("equation1", "eq2") rtl ("eq3", "eq4") in "target" subst (hov"x" -> le"f(f(c))")
   * }}}
   *
   * `ltr`: rewrite left-to-right using this equation
   * `rtl`: rewrite right-to-left using this equation
   * `many`: rewrite as long as possible (default is to only rewrite once)
   */
  def rewrite = RewriteTactic( equations = Seq(), target = None, once = true, fixedSubst = Map() )

  /**
   * Replaces a defined constant with its definition. Syntax:
   *
   * {{{
   *   unfold("def1", "def2",...,"defn") in ("label1", "label2",...,"labelk")
   * }}}
   *
   * NB: This will only replace the first definition it finds in each supplied formula. If you want to unfold all definitions,
   * use `repeat`.
   *
   * @param definitions The definitions `def1`,...,`defn`.
   * @param ctx         A [[context.Context]]. The definitions you want to unfold need to be present in `ctx`.
   */
  def unfold( definitions: String* )( implicit ctx: Context ) =
    UnfoldTacticHelper( definitions )

  /**
   * Does nothing.
   */
  def skip: Tactic[Unit] = Tactic.pure( () ).aka( "skip" )

  def now: Tactic[Unit] = new Tactic[Unit] {
    override def apply( proofState: ProofState ) =
      if ( proofState.isFinished ) Right( () -> proofState )
      else Left( TacticFailure( this, Some( proofState ), "not finished" ) )
    override def toString: String = "now"
  }

  /**
   * Retrieves the current subgoal.
   */
  case object currentGoal extends Tactical1[OpenAssumption] {
    def apply( goal: OpenAssumption ) = Tactic.pure( goal )
  }

  /** Instantiates prenex quantifiers to obtain a formula in a given polarity. */
  def haveInstance( formula: Formula, polarity: Polarity ): Tactic[String] = Tactic {
    def findInstances( labelledSequent: Sequent[( String, Formula )] ): Seq[( String, Seq[Expr] )] = {
      val quantifiedFormulas = labelledSequent.zipWithIndex.collect {
        case ( ( l, Ex.Block( vs, m ) ), i ) if i.isSuc && polarity.inSuc  => ( l, vs, m )
        case ( ( l, All.Block( vs, m ) ), i ) if i.isAnt && polarity.inAnt => ( l, vs, m )
      }
      for {
        ( l, vs, m ) <- quantifiedFormulas.elements
        subst <- syntacticMatching( List( m -> formula ), PreSubstitution( freeVariables( m ).diff( vs.toSet ).map( v => v -> v ) ) )
      } yield l -> subst( vs )
    }

    for {
      goal <- currentGoal
      inst <- findInstances( goal.labelledSequent ).headOption.
        toTactic( s"Could not find instance $formula in " + ( if ( polarity.inSuc ) "succedent" else "antecedent" ) )
      ( label, terms ) = inst
      newLabel <- if ( terms.isEmpty ) TacticMonad.pure( label ) else if ( polarity.inSuc ) exR( label, terms: _* ) else allL( label, terms: _* )
    } yield newLabel
  }

  def haveInstances( sequent: HOLSequent ): Tactic[Sequent[String]] =
    Tactic.sequence( for ( ( f, i ) <- sequent.zipWithIndex ) yield haveInstance( f, i.polarity ) )

  def treeGrammarInduction( implicit ctx: Context ): TreeGrammarInductionTactic = new TreeGrammarInductionTactic

  def analyticInduction( implicit ctx: MutableContext ) = AnalyticInductionTactic(
    StandardInductionAxioms(), Escargot )

  def anaInd( implicit ctx: Context ): Tactic[Unit] = {
    implicit val mutCtx = ctx.newMutable
    repeat( allR ) andThen AnalyticInductionTactic( StandardInductionAxioms(), Escargot.withDeskolemization )
  }
  def anaIndG( implicit ctx: Context ): Tactic[Unit] = {
    implicit val mutCtx = ctx.newMutable
    repeat( allR ) andThen AnalyticInductionTactic( GeneralInductionAxioms(), Escargot.withDeskolemization )
  }

  def escrgt( implicit ctx: Context ): Tactic[Unit] = {
    implicit val mutCtx = ctx.newMutable
    escargot.withDeskolemization
  }

  def introUnivsExcept( i: Int ): Tactic[Unit] = Tactic {
    for {
      goal <- currentGoal
      _ <- Tactic.guard( goal.conclusion.succedent.nonEmpty, "no formula in succedent" )
      q @ All.Block( xs, f ) = goal.conclusion.succedent.head
      _ <- Tactic.guard( i < xs.size, s"less than $i quantifiers" )
      newGoal = OpenAssumption( goal.labelledSequent.updated( Suc( 0 ), goal.labelledSequent( Suc( 0 ) )._1 -> All( xs( i ), f ) ) )
      _ <- insert( ForallRightBlock( CutRule( newGoal, ForallLeftRule( LogicalAxiom( f ), All( xs( i ), f ) ), All( xs( i ), f ) ), q, xs ) )
    } yield ()
  }

  def generalize( vs: Var* ): Tactic[Unit] = Tactic {
    for {
      goal <- currentGoal
      _ <- Tactic.guard( goal.conclusion.succedent.nonEmpty, "no formula in succedent" )
      q = goal.conclusion.succedent.head
      q_ = All.Block( vs, q )
      newGoal = OpenAssumption( goal.labelledSequent.updated( Suc( 0 ), goal.labelledSequent.succedent.head._1 -> q_ ) )
      _ <- insert( CutRule( newGoal, ForallLeftBlock( LogicalAxiom( q ), q_, vs ), q_ ) )
    } yield ()
  }

  def revert( hyps: String* ): Tactic[Unit] = Tactic {
    for {
      goal <- currentGoal
      _ <- Tactic.guard( goal.conclusion.succedent.nonEmpty, "no formula in succedent" )
      q = goal.conclusion.succedent.head
      hypFs = goal.labelledSequent.filter( hyps contains _._1 ).map( _._2 )
      q_ = hypFs.toNegConjunction --> q
      newGoal = OpenAssumption( goal.labelledSequent.updated( Suc( 0 ), goal.labelledSequent.succedent.head._1 -> q_ ).
        filterNot( hyps contains _._1 ) )
      p <- solvePropositional( q_ +: hypFs :+ q ).toTactic
      _ <- insert( CutRule( newGoal, p, q_ ) )
    } yield ()
  }

  def simp( implicit ctx: Context ): SimpTactic = SimpTactic()

  /** `by { tac1; tac2; ...; tacn }` solves the first goal using the provided tactic block, and fails otherwise */
  def by: TacticBlockArgument[Tactic[Unit]] =
    tac => tac.focused

  def trace( implicit sig: BabelSignature ): Tactic[Unit] =
    Tactic( currentGoal.map { g => println( g.toPrettyString ); () } )

  def subst1: SubstTactic = SubstTactic( UniqueFormula )
  def subst1( hyp: String ): SubstTactic = SubstTactic( OnLabel( hyp ) )
  def substAll: Tactic[Unit] = Tactic( repeat( SubstTactic( AnyFormula ) ) )
  def subst( hyps: String* ): Tactic[Unit] =
    Tactic( Tactic.sequence( for ( hyp <- hyps ) yield subst1( hyp ) ) andThen skip )

  def cases( lemma: String, terms: Expr* )( implicit ctx: Context ): Tactic[Unit] = casesW( lemma, lemma, terms: _* )
  def casesW( label: String, lemma: String, terms: Expr* )( implicit ctx: Context ): Tactic[Unit] = Tactic {
    def substOr( l: String ): Tactic[Unit] =
      ( orL( l ) onAll substOr( l ) ) orElse
        ( exL( l ) onAll substOr( l ) ) orElse
        subst1( l ) orElse skip
    for {
      _ <- include( label, ProofLink( lemma ) )
      _ <- allL( label, terms: _* ).forget
      _ <- substOr( label )
    } yield ()
  }
}