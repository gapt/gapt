package at.logic.gapt.proofs.gaptic

import tactics._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.ProofNames
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.viper.{ TreeGrammarInductionTactic, TreeGrammarInductionTactic2 }
import at.logic.gapt.provers.viper.aip.axioms.StandardInductionAxioms

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
  def trivial: Tactical[Unit] = Tactical { axiomTop orElse axiomBot orElse axiomRefl orElse axiomLog }.
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
   * @param ctx A [[at.logic.gapt.proofs.Context]]. It must contain an inductive definition of the type of `x`.
   */
  def induction( on: Var )( implicit ctx: Context ) = InductionTactic( UniqueFormula, on )

  /**
   * Applies the `Induction` tactic to the current subgoal: The goal
   *
   * `Γ, :- Δ, ∀x.A`
   *
   * is reduced to `n` new subgoals, where `n` is the number of constructors of the type of `x`.
   * @param label The label of the formula `∀x.A`.
   * @param ctx A [[at.logic.gapt.proofs.Context]]. It must contain an inductive definition of the type of `x`.
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
  def include( label: String, proof: LKProof ): Tactical[Unit] = Tactical {
    for {
      goal <- currentGoal
      diff = proof.conclusion diff goal.conclusion
      cutFormula = diff.toDisjunction
      _ <- cut( label, cutFormula )
      _ <- insert( proof )
    } yield ()
  }

  /**
   * Solves the current subgoal as a first-order consequence of the background theory. This
   * closes the goal.
   * @param ctx A [[at.logic.gapt.proofs.Context]]. The current subgoal must be contained in its background theory.
   */
  def foTheory( implicit ctx: Context ): Tactical[Unit] = Tactical {
    for {
      goal <- currentGoal
      theoryAxiom <- FOTheoryMacroRule.option( goal.conclusion collect { case a: Atom => a } ).
        toTactical( "does not follow from theory" )
      _ <- insert( theoryAxiom )
    } yield ()
  }

  /**
   * Declares the current subgoal as a theory axiom, i.e. a sequent that is contained in the background theory. This
   * closes the goal.
   * @param ctx A [[at.logic.gapt.proofs.Context]]. The current subgoal must be contained in its background theory.
   */
  def theory( implicit ctx: Context ): Tactical[Unit] = Tactical {
    for {
      goal <- currentGoal
      proofLinkName <- ctx.get[Context.ProofNames].find( goal.conclusion ).
        toTactical( "does not follow from theory" )
      _ <- insert( ProofLink( proofLinkName, ctx.get[ProofNames].lookup( proofLinkName ).get ) )
    } yield ()
  }

  /**
   * Repeats a tactical until it fails.
   * @param t A tactical.
   */
  def repeat[T]( t: Tactical[T] ) = RepeatTactic( t )

  /**
   * Leaves a hole in the current proof by inserting a dummy proof of the empty sequent.
   */
  @deprecated( "Proof not finished!", since = "the dawn of time" )
  def sorry: Tactical[Unit] = Tactical {
    for {
      goal <- currentGoal
      _ <- insert( ProofLink( foc"sorry", goal.conclusion ) )
    } yield ()
  }

  /**
   * Tactic that immediately fails.
   */
  def fail = new Tactical[Nothing] {
    def apply( proofState: ProofState ) = Left( TacticalFailure( this, Some( proofState ), "explicit fail" ) )
    override def toString = "fail"
  }

  // Complex

  /**
   * Decomposes the current subgoal by applying all "simple" rules as often as possible. These rules are:
   * - `¬:l` and `¬:r`
   * - `∧:l`
   * - `∨:r`
   * - `⊃:r`
   * - `∀:r`
   * - `∃:l`
   */
  def decompose: Tactical[Unit] = Tactical {
    repeat {
      NegLeftTactic( AnyFormula ) orElse NegRightTactic( AnyFormula ) orElse
        AndLeftTactic( AnyFormula ) orElse OrRightTactic( AnyFormula ) orElse ImpRightTactic( AnyFormula ) orElse
        ForallRightTactic( AnyFormula ) orElse ExistsLeftTactic( AnyFormula )
    }
  }

  def destruct( label: String ): Tactical[Any] = Tactical {
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

  /**
   * Calls `prover9` on the current subgoal.
   */
  def prover9( implicit ctx: MutableContext ): Prover9Tactic = Prover9Tactic()

  /**
   * Calls `escargot` on the current subgoal.
   */
  def escargot( implicit ctx: MutableContext ): Tactic[Unit] = EscargotTactic()

  /**
   * Lets you "forget" a sequence of formulas, i.e. the tactics version of the weakening rule.
   * The formulas with labels `L,,1,,,...,L,,n,,` will be removed from the current goal.
   * @param ls The labels `L,,1,,`,...,`,,Ln,,`.
   *
   */
  def forget( ls: String* ): Tactical[Unit] =
    Tactical( Tactical.sequence( ls map { label => WeakeningLeftTactic( label ) orElse WeakeningRightTactic( label ) } ).map( _ => () ) )

  def forget( pred: ( String, Formula ) => Boolean ): Tactical[Unit] = Tactical {
    for {
      goal <- currentGoal
      _ <- insert( OpenAssumption( goal.labelledSequent.filterNot( lf => pred( lf._1, lf._2 ) ) ) )
    } yield ()
  }

  /**
   * Moves the specified goal to the front of the goal list.
   * @param indexOfSubGoal The index of the goal.
   */
  def focus( indexOfSubGoal: Int ) = FocusTactical( Left( indexOfSubGoal ) )

  /**
   * Moves the specified goal to the front of the goal list.
   * @param indexOfSubGoal The index of the goal.
   */
  def focus( indexOfSubGoal: OpenAssumptionIndex ) = FocusTactical( Right( indexOfSubGoal ) )

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
   * @param definitions The definitions `def1`,...,`defn`.
   * @param ctx A [[at.logic.gapt.proofs.Context]]. The definitions you want to unfold need to be present in `ctx`.
   */
  def unfold( definitions: String* )( implicit ctx: Context ) =
    UnfoldTacticHelper( definitions )

  /**
   * Does nothing.
   */
  def skip: Tactical[Unit] = Tactical { proofState => Right( ( (), proofState ) ) }

  def now: Tactical[Unit] = new Tactical[Unit] {
    override def apply( proofState: ProofState ) =
      if ( proofState.isFinished ) Right( () -> proofState )
      else Left( TacticalFailure( this, Some( proofState ), "not finished" ) )
    override def toString: String = "now"
  }

  /**
   * Retrieves the current subgoal.
   */
  def currentGoal: Tactic[OpenAssumption] = new Tactic[OpenAssumption] {
    def apply( goal: OpenAssumption ) = Right( goal -> goal )
    override def toString = "currentGoal"
  }

  /** Instantiates prenex quantifiers to obtain a formula in a given polarity. */
  def haveInstance( formula: Formula, polarity: Polarity ): Tactical[String] = Tactical {
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
        toTactical( s"Could not find instance $formula in " + ( if ( polarity.inSuc ) "succedent" else "antecedent" ) )
      ( label, terms ) = inst
      newLabel <- if ( terms.isEmpty ) TacticalMonad.pure( label ) else if ( polarity.inSuc ) exR( label, terms: _* ) else allL( label, terms: _* )
    } yield newLabel
  }

  def haveInstances( sequent: HOLSequent ): Tactical[Sequent[String]] =
    Tactical.sequence( for ( ( f, i ) <- sequent.zipWithIndex ) yield haveInstance( f, i.polarity ) )

  def treeGrammarInduction( implicit ctx: Context ): TreeGrammarInductionTactic = new TreeGrammarInductionTactic

  def treeGrammarInduction2( implicit ctx: Context ): TreeGrammarInductionTactic2 = new TreeGrammarInductionTactic2

  def analyticInduction( implicit ctx: MutableContext ) = AnalyticInductionTactic(
    StandardInductionAxioms(), Escargot )

  def introUnivsExcept( i: Int ): Tactical[Unit] = Tactical {
    for {
      goal <- currentGoal
      _ <- Tactical.guard( goal.conclusion.succedent.nonEmpty, "no formula in succedent" )
      q @ All.Block( xs, f ) = goal.conclusion.succedent.head
      _ <- Tactical.guard( i < xs.size, s"less than $i quantifiers" )
      newGoal = OpenAssumption( goal.labelledSequent.updated( Suc( 0 ), goal.labelledSequent( Suc( 0 ) )._1 -> All( xs( i ), f ) ) )
      _ <- insert( ForallRightBlock( CutRule( newGoal, ForallLeftRule( LogicalAxiom( f ), All( xs( i ), f ) ), All( xs( i ), f ) ), q, xs ) )
    } yield ()
  }
}