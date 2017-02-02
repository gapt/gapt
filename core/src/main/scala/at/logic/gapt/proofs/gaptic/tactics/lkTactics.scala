package at.logic.gapt.proofs.gaptic.tactics

import at.logic.gapt.expr.{ Apps, _ }
import at.logic.gapt.expr.hol.{ HOLPosition, instantiate }
import at.logic.gapt.proofs.Context.ProofNames
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk._

import scalaz._
import Scalaz._
import Validation.FlatMap._

/**
 * Closes a goal with a proof link
 *
 * @param proofName The name of the proof proving the goal.
 */
case class ProofLinkTactic( proofName: String )( implicit ctx: Context ) extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) = {
    val theProof = ctx.get[ProofNames].names.fold( None: Option[( LambdaExpression, Sequent[HOLFormula] )] )( ( rightProof, proofInCtx ) => {
      rightProof match {
        case Some( thing ) => Some( thing )
        case None => proofInCtx match {
          case ( Apps( at.logic.gapt.expr.Const( proofInCtxName, t ), args ), es: Sequent[HOLFormula] ) =>
            if ( proofName == proofInCtxName ) {
              val theSubs: Option[Substitution] = clauseSubsumption( es, goal.conclusion )
              theSubs match {
                case Some( sub ) => {
                  println( "four" )
                  Some( ( sub( Apps( at.logic.gapt.expr.Const( proofInCtxName, t ), args ) ), sub( es ) ) )
                }
                case None => {
                  println( "three" )
                  None
                }
              }
            } else {
              println( "two" )
              None
            }
          case _ => {
            println( "one" )
            None
          }
        }
      }

    } )
    theProof match {
      case Some( ( l: LambdaExpression, es: Sequent[HOLFormula] ) ) => ( (), ProofLink( l, es ) ).success
      case None => TacticalFailure( this, Some( goal ), "Cannot be proven from the specified proof" ).failureNel
    }

  }
}
/**
 * Closes a goal of the form A, Γ :- Δ, Δ
 */
case object LogicalAxiomTactic extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) = {
    val candidates = goal.conclusion.antecedent intersect goal.conclusion.succedent

    candidates match {
      case Seq( formula, _* ) => ( (), LogicalAxiom( formula ) ).success
      case _                  => TacticalFailure( this, Some( goal ), "not a logical axiom" ).failureNel
    }
  }
}

/**
 * Closes a goal of the form Γ :- Δ, ⊤
 */
case object TopAxiomTactic extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for ( ( _, Top(), _: Suc ) <- findFormula( goal, AnyFormula ) )
      yield () -> TopAxiom
}

/**
 * Closes a goal of the form ⊥, Γ :- Δ
 */
case object BottomAxiomTactic extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for ( ( _, Bottom(), _: Ant ) <- findFormula( goal, AnyFormula ) )
      yield () -> BottomAxiom
}

/**
 * Closes a goal of the form Γ :- Δ, s = s
 */
case object ReflexivityAxiomTactic extends Tactic[Unit] {
  object Refl {
    def unapply( f: HOLFormula ): Option[LambdaExpression] = f match {
      case Eq( t, t_ ) if t == t_ => Some( t )
      case _                      => None
    }
  }

  def apply( goal: OpenAssumption ) =
    for ( ( _, Refl( t ), _: Suc ) <- findFormula( goal, AnyFormula ) )
      yield () -> ReflexivityAxiom( t )
}

/**
 * Decomposes a negation in the antecedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 */
case class NegLeftTactic( mode: TacticApplyMode = UniqueFormula ) extends Tactic[String] {
  def apply( goal: OpenAssumption ) =
    for {
      ( existingLabel, Neg( f ), i: Ant ) <- findFormula( goal, mode )
      newGoal = goal.labelledSequent.delete( i ) :+ ( existingLabel -> f )
    } yield existingLabel -> NegLeftRule( OpenAssumption( newGoal ), newGoal.indices.last )
}

/**
 * Decomposes a negation in the succedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 */
case class NegRightTactic( mode: TacticApplyMode = UniqueFormula ) extends Tactic[String] {
  def apply( goal: OpenAssumption ) =
    for {
      ( existingLabel, Neg( f ), i: Suc ) <- findFormula( goal, mode )
      newGoal = ( existingLabel -> f ) +: goal.labelledSequent.delete( i )
    } yield existingLabel -> NegRightRule( OpenAssumption( newGoal ), newGoal.indices.head )
}

/**
 * Removes a formula from the antecedent of a goal.
 *
 * @param applyToLabel The label of the formula to be removed.
 */
case class WeakeningLeftTactic( applyToLabel: String ) extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for ( ( _, f, i: Ant ) <- findFormula( goal, OnLabel( applyToLabel ) ) )
      yield () -> OpenAssumption( goal.labelledSequent delete i )
}

/**
 * Removes a formula from the succedent of a goal.
 *
 * @param applyToLabel The label of the formula to be removed.
 */
case class WeakeningRightTactic( applyToLabel: String ) extends Tactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for ( ( _, f, i: Suc ) <- findFormula( goal, OnLabel( applyToLabel ) ) )
      yield () -> OpenAssumption( goal.labelledSequent delete i )
}

/**
 * Decomposes a conjunction in the antecedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 */
case class AndLeftTactic( mode: TacticApplyMode = UniqueFormula ) extends Tactic[( String, String )] {
  def apply( goal: OpenAssumption ) =
    for {
      ( label, And( lhs, rhs ), idx: Ant ) <- findFormula( goal, mode )
      newLabel1 #:: newLabel2 #:: _ = NewLabels( goal.labelledSequent, label )
      newGoal = ( newLabel1 -> lhs ) +: ( newLabel2 -> rhs ) +: goal.labelledSequent.delete( idx )
    } yield ( newLabel1, newLabel2 ) -> AndLeftRule( OpenAssumption( newGoal ), Ant( 0 ), Ant( 1 ) )
}

/**
 * Decomposes a conjunction in the succedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 */
case class AndRightTactic( mode: TacticApplyMode = UniqueFormula ) extends BinaryTactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for ( ( label, And( lhs, rhs ), idx: Suc ) <- findFormula( goal, mode ) )
      yield () ->
      AndRightRule( OpenAssumption( goal.labelledSequent.updated( idx, label -> lhs ) ), idx,
        OpenAssumption( goal.labelledSequent.updated( idx, label -> rhs ) ), idx )
}

/**
 * Decomposes a disjunction in the antecedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 */
case class OrLeftTactic( mode: TacticApplyMode = UniqueFormula ) extends BinaryTactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for ( ( label, Or( lhs, rhs ), idx: Ant ) <- findFormula( goal, mode ) )
      yield () ->
      OrLeftRule( OpenAssumption( goal.labelledSequent.updated( idx, label -> lhs ) ), idx,
        OpenAssumption( goal.labelledSequent.updated( idx, label -> rhs ) ), idx )
}

/**
 * Decomposes a disjunction in the succedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 */
case class OrRightTactic( mode: TacticApplyMode = UniqueFormula ) extends Tactic[( String, String )] {
  def apply( goal: OpenAssumption ) =
    for {
      ( label, Or( lhs, rhs ), idx: Suc ) <- findFormula( goal, mode )
      newLabel1 #:: newLabel2 #:: _ = NewLabels( goal.labelledSequent, label )
      newGoal = goal.labelledSequent.delete( idx ) :+ ( newLabel1 -> lhs ) :+ ( newLabel2 -> rhs )
      Seq( rhsIdx, lhsIdx ) = newGoal.indices.reverse.take( 2 )
    } yield ( newLabel1, newLabel2 ) -> OrRightRule( OpenAssumption( newGoal ), lhsIdx, rhsIdx )
}

/**
 * Decomposes an implication in the antecedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 */
case class ImpLeftTactic( mode: TacticApplyMode = UniqueFormula ) extends BinaryTactic[Unit] {
  def apply( goal: OpenAssumption ) =
    for ( ( label, Imp( lhs, rhs ), idx: Ant ) <- findFormula( goal, mode ) )
      yield () ->
      ImpLeftRule( OpenAssumption( goal.labelledSequent.delete( idx ) :+ ( label -> lhs ) ), Suc( goal.labelledSequent.succedent.size ),
        OpenAssumption( goal.labelledSequent.updated( idx, label -> rhs ) ), idx )
}

/**
 * Decomposes an implication in the succedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 */
case class ImpRightTactic( mode: TacticApplyMode = UniqueFormula ) extends Tactic[( String, String )] {
  // TODO: keep label for rhs?
  def apply( goal: OpenAssumption ) =
    for {
      ( label, Imp( lhs, rhs ), idx: Suc ) <- findFormula( goal, mode )
      newLabel1 #:: newLabel2 #:: _ = NewLabels( goal.labelledSequent, label )
      newGoal = ( newLabel1 -> lhs ) +: goal.labelledSequent.updated( idx, newLabel2 -> rhs )
    } yield ( newLabel1, newLabel2 ) -> ImpRightRule( OpenAssumption( newGoal ), Ant( 0 ), idx )
}

abstract class StrongQuantTactic extends Tactic[Var] {
  def eigenVariable: Option[Var]
  protected def pickEigenvariable( bound: Var, goal: OpenAssumption ) =
    eigenVariable match {
      case Some( ev ) =>
        if ( freeVariables( goal.conclusion ) contains ev )
          TacticalFailure( this, Some( goal ), "Provided eigenvariable would violate eigenvariable condition." ).failureNel
        else
          ev.success
      case None =>
        rename( bound, freeVariables( goal.conclusion ) ).success
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
    } yield ev -> ExistsLeftRule( OpenAssumption( goal.labelledSequent.updated( idx, label -> instantiate( f, ev ) ) ), f, ev )
}

/**
 * Decomposes a block of existential quantifiers in the antecedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 * @param terms Instantiations for the quantifiers in the block.
 * @param instantiateOnce Whether the quantified formula should be forgotten after instantiating.
 */
case class ExistsRightTactic( mode: TacticApplyMode = UniqueFormula, terms: Seq[LambdaExpression], instantiateOnce: Boolean ) extends Tactic[String] {
  def apply( goal: OpenAssumption ) =
    for {
      ( label: String, f @ Ex( _, _ ), idx: Suc ) <- findFormula( goal, mode )
      newLabel = NewLabel( goal.labelledSequent, label )
      instantiatedFormula = BetaReduction.betaNormalize( instantiate( f, terms ) )
    } yield if ( instantiateOnce ) {
      label ->
        ExistsRightBlock( OpenAssumption( goal.labelledSequent.updated( idx, ( label, instantiatedFormula ) ) ), f, terms )
    } else {
      newLabel ->
        ExistsRightBlock( OpenAssumption( goal.labelledSequent :+ ( newLabel -> instantiatedFormula ) ), f, terms )
    }

  def forget = ExistsRightTactic( mode, terms, instantiateOnce = true )
}

/**
 * Decomposes a block of universal quantifiers in the succedent of a goal.
 *
 * @param mode How to apply the tactic: To a specific label, to the only fitting formula, or to any fitting formula.
 * @param terms Instantiations for the quantifiers in the block.
 * @param instantiateOnce Whether the quantified formula should be forgotten after instantiating.
 */
case class ForallLeftTactic( mode: TacticApplyMode = UniqueFormula, terms: Seq[LambdaExpression], instantiateOnce: Boolean ) extends Tactic[String] {
  def apply( goal: OpenAssumption ) =
    for {
      ( label: String, f @ All( _, _ ), idx: Ant ) <- findFormula( goal, mode )
      newLabel = NewLabel( goal.labelledSequent, label )
      instantiatedFormula = BetaReduction.betaNormalize( instantiate( f, terms ) )
    } yield if ( instantiateOnce ) {
      label ->
        ForallLeftBlock( OpenAssumption( goal.labelledSequent.updated( idx, ( label, instantiatedFormula ) ) ), f, terms )
    } else {
      newLabel ->
        ForallLeftBlock( OpenAssumption( ( newLabel -> instantiatedFormula ) +: goal.labelledSequent ), f, terms )
    }

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
    } yield ev -> ForallRightRule( OpenAssumption( goal.labelledSequent.updated( idx, label -> instantiate( f, ev ) ) ), f, ev )
}

/**
 * Introduces a cut, creating two new subgoals.
 *
 * @param cutFormula The cut formula.
 * @param cutLabel The label for the cut formula.
 */
case class CutTactic( cutLabel: String, cutFormula: HOLFormula ) extends BinaryTactic[Unit] {
  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.labelledSequent

    val leftPremise = OpenAssumption( goalSequent :+ ( cutLabel, cutFormula ) )
    val rightPremise = OpenAssumption( ( cutLabel, cutFormula ) +: goalSequent )

    val auxProof = CutRule( leftPremise, Suc( leftPremise.labelledSequent.succedent.length - 1 ), rightPremise, Ant( 0 ) )
    ( () -> auxProof ).success
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
case class EqualityTactic( equationLabel: String, formulaLabel: String, leftToRight: Option[Boolean] = None, targetFormula: Option[HOLFormula] = None ) extends Tactic[Unit] {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.labelledSequent

    val indices = for (
      ( ( `equationLabel`, Eq( _, _ ) ), eqIndex ) <- goalSequent.zipWithIndex.antecedent;
      ( ( `formulaLabel`, _ ), formulaIndex ) <- goalSequent.zipWithIndex.elements
    ) yield ( eqIndex, formulaIndex )

    indices.headOption match {
      case None => TacticalFailure( this, Some( goal ), "label not found" ).failureNel
      case Some( ( equalityIndex, formulaIndex ) ) =>
        val ( _, Eq( s, t ) ) = goalSequent( equalityIndex )
        val ( _, auxFormula ) = goalSequent( formulaIndex )

        def f( l: List[HOLPosition], h: HOLFormula, r: LambdaExpression ): HOLFormula = l match {
          case x :: xs => f( xs, h.replace( x, r ), r )
          case Nil     => h
        }

        def testValidity( mainFormula: HOLFormula ): Boolean = {
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

            ( (), if ( formulaIndex.isAnt ) EqualityLeftRule( premise, equalityIndex, formulaIndex, auxFormula ) else EqualityRightRule( premise, equalityIndex, formulaIndex, auxFormula ) ).success
          case _ => TacticalFailure( this, Some( goal ), "FIXME" ).failureNel
        }
    }
  }

  def fromLeftToRight = new EqualityTactic( equationLabel, formulaLabel, leftToRight = Some( true ) )

  def fromRightToLeft = new EqualityTactic( equationLabel, formulaLabel, leftToRight = Some( false ) )

  def yielding( targetFormula: HOLFormula ) = new EqualityTactic( equationLabel, formulaLabel, targetFormula = Some( targetFormula ) )
}
