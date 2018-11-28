package gapt.proofs.gaptic.tactics

import gapt.expr._
import gapt.expr.hol.HOLPosition
import gapt.expr.hol.instantiate
import gapt.proofs._
import gapt.proofs.context.Context
import gapt.proofs.context.facet.ProofNames
import gapt.proofs.gaptic._
import gapt.proofs.lk._

/**
 * Closes a goal with a proof link
 *
 * @param proofName The name of the proof proving the goal.
 */
case class ProofLinkTactic( proofName: String )( implicit ctx: Context ) extends Tactical1[Unit] {
  def apply( goal: OpenAssumption ) = ctx.get[ProofNames].names.get( proofName ) match {
    case Some( ( term, refSeq ) ) => clauseSubsumption( refSeq, goal.conclusion, multisetSubsumption = true ) match {
      case Some( sub ) => replace( ProofLink( sub( term ), sub( refSeq ) ) )
      case None        => TacticFailure( this, "Mismatch between  goal " + goal.toString + " and  Referenced Sequent " + refSeq.toString )
    }
    case None => TacticFailure( this, "Proof " + proofName + " not defined in context" )
  }
}
/**
 * Closes a goal of the form A, Γ :- Δ, Δ
 */
case object LogicalAxiomTactic extends Tactical1[Unit] {
  def apply( goal: OpenAssumption ) = {
    val candidates = goal.conclusion.antecedent intersect goal.conclusion.succedent

    candidates match {
      case Seq( formula, _* ) => replace( LogicalAxiom( formula ) )
      case _                  => TacticFailure( this, "not a logical axiom" )
    }
  }
}

/**
 * Closes a goal of the form Γ :- Δ, ⊤
 */
case object TopAxiomTactic extends Tactical1[Unit] {
  def apply( goal: OpenAssumption ): Tactic[Unit] =
    for {
      ( _, Top(), _: Suc ) <- findFormula( goal, AnyFormula )
      _ <- replace( TopAxiom )
    } yield ()
}

/**
 * Closes a goal of the form ⊥, Γ :- Δ
 */
case object BottomAxiomTactic extends Tactical1[Unit] {
  def apply( goal: OpenAssumption ): Tactic[Unit] =
    for {
      ( _, Bottom(), _: Ant ) <- findFormula( goal, AnyFormula )
      _ <- replace( BottomAxiom )
    } yield ()
}

/**
 * Closes a goal of the form Γ :- Δ, s = s
 */
case object ReflexivityAxiomTactic extends Tactical1[Unit] {
  object Refl {
    def unapply( f: Formula ): Option[Expr] = f match {
      case Eq( t, t_ ) if t == t_ => Some( t )
      case _                      => None
    }
  }

  def apply( goal: OpenAssumption ) =
    for {
      ( _, Refl( t ), _: Suc ) <- findFormula( goal, AnyFormula )
      _ <- replace( ReflexivityAxiom( t ) )
    } yield ()
}

/**
 * Decomposes a negation in the antecedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 */
case class NegLeftTactic( mode: TacticApplyMode = UniqueFormula ) extends Tactical1[String] {
  def apply( goal: OpenAssumption ) =
    for {
      ( existingLabel: String, Neg( f ), i: Ant ) <- findFormula( goal, mode )
      newGoal = goal.labelledSequent.delete( i ) :+ ( existingLabel -> f )
      _ <- replace( NegLeftRule( OpenAssumption( newGoal ), newGoal.indices.last ) )
    } yield existingLabel
}

/**
 * Decomposes a negation in the succedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 */
case class NegRightTactic( mode: TacticApplyMode = UniqueFormula ) extends Tactical1[String] {
  def apply( goal: OpenAssumption ) =
    for {
      ( existingLabel: String, Neg( f ), i: Suc ) <- findFormula( goal, mode )
      newGoal = ( existingLabel -> f ) +: goal.labelledSequent.delete( i )
      _ <- replace( NegRightRule( OpenAssumption( newGoal ), newGoal.indices.head ) )
    } yield existingLabel
}

/**
 * Removes a formula from the antecedent of a goal.
 *
 * @param applyToLabel The label of the formula to be removed.
 */
case class WeakeningLeftTactic( applyToLabel: String ) extends Tactical1[Unit] {
  def apply( goal: OpenAssumption ) =
    for {
      ( _, _, i: Ant ) <- findFormula( goal, OnLabel( applyToLabel ) )
      _ <- replace( OpenAssumption( goal.labelledSequent delete i ) )
    } yield ()
}

/**
 * Removes a formula from the succedent of a goal.
 *
 * @param applyToLabel The label of the formula to be removed.
 */
case class WeakeningRightTactic( applyToLabel: String ) extends Tactical1[Unit] {
  def apply( goal: OpenAssumption ) =
    for {
      ( _, _, i: Suc ) <- findFormula( goal, OnLabel( applyToLabel ) )
      _ <- replace( OpenAssumption( goal.labelledSequent delete i ) )
    } yield ()
}

/**
 * Decomposes a conjunction in the antecedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 */
case class AndLeftTactic( mode: TacticApplyMode = UniqueFormula ) extends Tactical1[( String, String )] {
  def apply( goal: OpenAssumption ) =
    for {
      ( label, And( lhs, rhs ), idx: Ant ) <- findFormula( goal, mode )
      newLabel1 #:: newLabel2 #:: _ = NewLabels( goal.labelledSequent, label )
      newGoal = ( newLabel1 -> lhs ) +: ( newLabel2 -> rhs ) +: goal.labelledSequent.delete( idx )
      _ <- replace( AndLeftRule( OpenAssumption( newGoal ), Ant( 0 ), Ant( 1 ) ) )
    } yield ( newLabel1, newLabel2 )
}

/**
 * Decomposes a conjunction in the succedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 */
case class AndRightTactic( mode: TacticApplyMode = UniqueFormula ) extends Tactical1[Unit] with BinaryTactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for {
      ( label, And( lhs, rhs ), idx: Suc ) <- findFormula( goal, mode )
      _ <- replace(
        AndRightRule( OpenAssumption( goal.labelledSequent.updated( idx, label -> lhs ) ), idx,
          OpenAssumption( goal.labelledSequent.updated( idx, label -> rhs ) ), idx ) )
    } yield ()
}

/**
 * Decomposes a disjunction in the antecedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 */
case class OrLeftTactic( mode: TacticApplyMode = UniqueFormula ) extends Tactical1[Unit] with BinaryTactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for {
      ( label, Or( lhs, rhs ), idx: Ant ) <- findFormula( goal, mode )
      _ <- replace(
        OrLeftRule( OpenAssumption( goal.labelledSequent.updated( idx, label -> lhs ) ), idx,
          OpenAssumption( goal.labelledSequent.updated( idx, label -> rhs ) ), idx ) )
    } yield ()
}

/**
 * Decomposes a disjunction in the succedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 */
case class OrRightTactic( mode: TacticApplyMode = UniqueFormula ) extends Tactical1[( String, String )] {
  def apply( goal: OpenAssumption ) =
    for {
      ( label, Or( lhs, rhs ), idx: Suc ) <- findFormula( goal, mode )
      newLabel1 #:: newLabel2 #:: _ = NewLabels( goal.labelledSequent, label )
      newGoal = goal.labelledSequent.delete( idx ) :+ ( newLabel1 -> lhs ) :+ ( newLabel2 -> rhs )
      Seq( rhsIdx, lhsIdx ) = newGoal.indices.reverse.take( 2 )
      _ <- replace( OrRightRule( OpenAssumption( newGoal ), lhsIdx, rhsIdx ) )
    } yield ( newLabel1, newLabel2 )
}

/**
 * Decomposes an implication in the antecedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 */
case class ImpLeftTactic( mode: TacticApplyMode = UniqueFormula ) extends Tactical1[Unit] with BinaryTactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for {
      ( label, Imp( lhs, rhs ), idx: Ant ) <- findFormula( goal, mode )
      _ <- replace(
        ImpLeftRule( OpenAssumption( goal.labelledSequent.delete( idx ) :+ ( label -> lhs ) ), Suc( goal.labelledSequent.succedent.size ),
          OpenAssumption( goal.labelledSequent.updated( idx, label -> rhs ) ), idx ) )
    } yield ()
}

/**
 * Decomposes an implication in the succedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 */
case class ImpRightTactic( mode: TacticApplyMode = UniqueFormula ) extends Tactical1[( String, String )] {
  // TODO: keep label for rhs?
  def apply( goal: OpenAssumption ) =
    for {
      ( label, Imp( lhs, rhs ), idx: Suc ) <- findFormula( goal, mode )
      newLabel1 #:: newLabel2 #:: _ = NewLabels( goal.labelledSequent, label )
      newGoal = ( newLabel1 -> lhs ) +: goal.labelledSequent.updated( idx, newLabel2 -> rhs )
      _ <- replace( ImpRightRule( OpenAssumption( newGoal ), Ant( 0 ), idx ) )
    } yield ( newLabel1, newLabel2 )
}

abstract class StrongQuantTactic extends Tactical1[Var] {
  def eigenVariable: Option[Var]
  protected def pickEigenvariable( bound: Var, goal: OpenAssumption ): Tactic[Var] =
    eigenVariable match {
      case Some( ev ) =>
        if ( freeVariables( goal.conclusion ) contains ev )
          TacticFailure( this, "Provided eigenvariable would violate eigenvariable condition." )
        else
          Tactic.pure( ev )
      case None =>
        Tactic.pure( rename( bound, freeVariables( goal.conclusion ) ) )
    }
}

/**
 * Decomposes an existential quantifier in the antecedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 * @param eigenVariable If Some(v), the rule will attempt to use v as the eigenvariable. Otherwise it will automatically pick one.
 */
case class ExistsLeftTactic( mode: TacticApplyMode = UniqueFormula, eigenVariable: Option[Var] = None ) extends StrongQuantTactic {
  def apply( goal: OpenAssumption ) =
    for {
      ( label, f @ Ex( bound, _ ), idx: Ant ) <- findFormula( goal, mode )
      ev <- pickEigenvariable( bound, goal )
      _ <- replace( ExistsLeftRule( OpenAssumption( goal.labelledSequent.updated( idx, label -> instantiate( f, ev ) ) ), f, ev ) )
    } yield ev
}

/**
 * Decomposes a block of existential quantifiers in the antecedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 * @param terms Instantiations for the quantifiers in the block.
 * @param instantiateOnce Whether the quantified formula should be forgotten after instantiating.
 */
case class ExistsRightTactic( mode: TacticApplyMode = UniqueFormula, terms: Seq[Expr], instantiateOnce: Boolean ) extends Tactical1[String] {
  def apply( goal: OpenAssumption ) =
    for {
      ( label: String, f @ Ex( _, _ ), idx: Suc ) <- findFormula( goal, mode )
      newLabel = NewLabel( goal.labelledSequent, label )
      instantiatedFormula = BetaReduction.betaNormalize( instantiate( f, terms ) )
      newLS = if ( instantiateOnce ) goal.labelledSequent.updated( idx, ( label, instantiatedFormula ) )
      else goal.labelledSequent :+ ( newLabel -> instantiatedFormula )
      _ <- replace( ExistsRightBlock( OpenAssumption( newLS ), f, terms ) )
    } yield if ( instantiateOnce ) label else newLabel

  def forget = ExistsRightTactic( mode, terms, instantiateOnce = true )
}

/**
 * Decomposes a block of universal quantifiers in the succedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 * @param terms Instantiations for the quantifiers in the block.
 * @param instantiateOnce Whether the quantified formula should be forgotten after instantiating.
 */
case class ForallLeftTactic( mode: TacticApplyMode = UniqueFormula, terms: Seq[Expr], instantiateOnce: Boolean ) extends Tactical1[String] {
  def apply( goal: OpenAssumption ) =
    for {
      ( label: String, f @ All( _, _ ), idx: Ant ) <- findFormula( goal, mode )
      newLabel = NewLabel( goal.labelledSequent, label )
      instantiatedFormula = BetaReduction.betaNormalize( instantiate( f, terms ) )
      newLS = if ( instantiateOnce ) goal.labelledSequent.updated( idx, ( label, instantiatedFormula ) )
      else ( newLabel -> instantiatedFormula ) +: goal.labelledSequent
      _ <- replace( ForallLeftBlock( OpenAssumption( newLS ), f, terms ) )
    } yield if ( instantiateOnce ) label else newLabel

  def forget = ForallLeftTactic( mode, terms, instantiateOnce = true )
}

/**
 * Decomposes a universal quantifier in the succedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 * @param eigenVariable If Some(v), the rule will attempt to use v as the eigenvariable. Otherwise it will automatically pick one.
 */
case class ForallRightTactic( mode: TacticApplyMode = UniqueFormula, eigenVariable: Option[Var] = None ) extends StrongQuantTactic {
  def apply( goal: OpenAssumption ) =
    for {
      ( label, f @ All( bound, _ ), idx: Suc ) <- findFormula( goal, mode )
      ev <- pickEigenvariable( bound, goal )
      _ <- replace( ForallRightRule( OpenAssumption( goal.labelledSequent.updated( idx, label -> instantiate( f, ev ) ) ), f, ev ) )
    } yield ev
}

/**
 * Introduces a cut, creating two new subgoals.
 *
 * @param cutFormula The cut formula.
 * @param cutLabel The label for the cut formula.
 */
case class CutTactic( cutLabel: String, cutFormula: Formula ) extends Tactical1[Unit] with BinaryTactic[Unit] {
  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.labelledSequent

    val leftPremise = OpenAssumption( goalSequent :+ ( cutLabel, cutFormula ) )
    val rightPremise = OpenAssumption( ( cutLabel, cutFormula ) +: goalSequent )

    val auxProof = CutRule( leftPremise, Suc( leftPremise.labelledSequent.succedent.length - 1 ), rightPremise, Ant( 0 ) )
    replace( auxProof )
  }
}

/**
 * Applies an equation in a goal.
 *
 * @param equationLabel The label of the equation.
 * @param formulaLabel The label of the formula the equation is to be used on.
 * @param leftToRight If `Some(true)`, the equation `s = t` will be used to rewrite `s` to `t`, and the other way around
 *                    for Some(false). If `None`, the tactic will attempt to decide the direction automatically.
 * @param targetFormula If `Some(f)`, the tactic will attempt to produce `f` through application of the equality. Otherwise
 *                      it will replace as many occurrences as possible according to `leftToRight`.
 */
case class EqualityTactic( equationLabel: String, formulaLabel: String, private val leftToRight: Option[Boolean] = None, private val targetFormula: Option[Formula] = None ) extends Tactical1[Unit] {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.labelledSequent

    val indices = for (
      ( ( `equationLabel`, Eq( _, _ ) ), eqIndex ) <- goalSequent.zipWithIndex.antecedent;
      ( ( `formulaLabel`, _ ), formulaIndex ) <- goalSequent.zipWithIndex.elements
    ) yield ( eqIndex, formulaIndex )

    indices.headOption match {
      case None => TacticFailure( this, "label not found" )
      case Some( ( equalityIndex, formulaIndex ) ) =>
        val ( _, Eq( s, t ) ) = goalSequent( equalityIndex )
        val ( _, auxFormula ) = goalSequent( formulaIndex )

        def f( l: List[HOLPosition], h: Formula, r: Expr ): Formula = l match {
          case x :: xs => f( xs, h.replace( x, r ), r )
          case Nil     => h
        }

        def testValidity( mainFormula: Formula ): Boolean = {
          if ( s == t && auxFormula == mainFormula ) {
            val sAux = auxFormula.find( s )

            if ( sAux.isEmpty )
              false
            else
              true
          } else if ( s == t && auxFormula != mainFormula )
            false
          else if ( s != t && auxFormula == mainFormula )
            false
          else {
            val sAux = auxFormula.find( s )
            val sMain = mainFormula.find( s )

            val tAux = auxFormula.find( t )
            val tMain = mainFormula.find( t )

            if ( sAux.isEmpty && tAux.isEmpty )
              false
            else {
              val tToS = sMain intersect tAux
              val sToT = tMain intersect sAux

              if ( tToS.isEmpty ) {
                val mainNew = sToT.foldLeft( auxFormula ) { ( acc, p ) => HOLPosition.replace( acc, p, t ) }
                if ( mainNew == mainFormula )
                  true
                else
                  false
              } else if ( sToT.isEmpty ) {
                val mainNew = tToS.foldLeft( auxFormula ) { ( acc, p ) => HOLPosition.replace( acc, p, s ) }
                if ( mainNew == mainFormula )
                  true
                else
                  false
              } else
                false
            }
          }
        }

        val replacement = targetFormula match {
          case Some( mainFormula ) =>
            if ( testValidity( mainFormula ) )
              targetFormula
            else None
          case None =>
            val r = leftToRight match {
              case Some( true ) =>
                f( auxFormula.find( s ), auxFormula, t )
              case Some( false ) =>
                f( auxFormula.find( t ), auxFormula, s )
              case None =>
                ( auxFormula.find( s ), auxFormula.find( t ) ) match {
                  case ( Nil, ps ) if ps.nonEmpty =>
                    f( ps, auxFormula, s )
                  case ( ps, Nil ) if ps.nonEmpty =>
                    f( ps, auxFormula, t )
                }
            }

            Option( r )

          case _ => None
        }

        replacement match {
          case Some( x ) if x != auxFormula =>
            val newGoal = goalSequent.updated( formulaIndex, formulaLabel -> x )
            val premise = OpenAssumption( newGoal )

            replace( if ( formulaIndex.isAnt ) EqualityLeftRule( premise, equalityIndex, formulaIndex, auxFormula )
            else EqualityRightRule( premise, equalityIndex, formulaIndex, auxFormula ) )
          case _ => TacticFailure( this, "FIXME" )
        }
    }
  }

  def fromLeftToRight = EqualityTactic( equationLabel, formulaLabel, leftToRight = Some( true ) )

  def fromRightToLeft = EqualityTactic( equationLabel, formulaLabel, leftToRight = Some( false ) )

  def yielding( targetFormula: Formula ) = EqualityTactic( equationLabel, formulaLabel, targetFormula = Some( targetFormula ) )
}
