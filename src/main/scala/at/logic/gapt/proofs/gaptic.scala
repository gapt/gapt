package at.logic.gapt.proofs

import at.logic.gapt.expr._
import at.logic.gapt.proofs.lkNew._

/**
 * Immutable object defining the current state of the proof in the tactics language.
 * @param initSequent
 * @param currentGoalIndex
 * @param proofSegment
 */
case class ProofState( val initSequent: Sequent[( HOLFormula, String )], val currentGoalIndex: Int, val proofSegment: LKProof ) {
  val subGoals: Seq[OpenAssumption] =
    for ( OpenAssumption( s ) <- proofSegment.postOrder )
      yield OpenAssumption( s )

  require( currentGoalIndex >= 0 && currentGoalIndex <= subGoals.length )

  /**
   *
   * Constructor with name of theorem and initial formula.
   */
  def this( initSequent: Sequent[( HOLFormula, String )] ) = this( initSequent, 0, OpenAssumption( initSequent ) )

  /**
   * Returns the sub goal at a given index if it exists.
   * @param i
   * @return
   */
  def getSubGoal( i: Int ): Option[OpenAssumption] = Some( subGoals( i ) )

  /**
   * Returns a string representation of a sub goal at a given index.
   * @param i
   * @return
   */
  def displaySubGoal( i: Int ): String = {
    getSubGoal( i ).toString
  }

  /**
   * Replaces the i-th open assumption by an arbitrary proof segment and returns the result in a new proof state.
   * @param openAssumption
   * @param replacementSegment
   * @return
   */
  def replaceSubGoal( openAssumption: Int, replacementSegment: LKProof ): ProofState = {
    var assumptionIndex = -1

    // Replacement function - applied recursively
    def f( p: LKProof ): LKProof = p match {
      // Open assumption. Replace on matching index.
      case OpenAssumption( _ ) =>
        assumptionIndex += 1
        if ( assumptionIndex == openAssumption )
          replacementSegment
        else
          p
      // Case distinction on rules
      case InitialSequent( s )                                         => Axiom( s )
      case ContractionLeftRule( subProof, index1, _ )                  => ContractionLeftRule( f( subProof ), subProof.conclusion( index1 ) )
      case ContractionRightRule( subProof, index1, _ )                 => ContractionRightRule( f( subProof ), subProof.conclusion( index1 ) )
      case WeakeningLeftRule( subProof, formula )                      => WeakeningLeftRule( f( subProof ), formula )
      case WeakeningRightRule( subProof, formula )                     => WeakeningRightRule( f( subProof ), formula )
      case CutRule( leftSubProof, index1, rightSubProof, index2 )      => CutRule( f( leftSubProof ), leftSubProof.conclusion( index1 ), f( rightSubProof ), rightSubProof.conclusion( index2 ) )
      case NegLeftRule( subProof, index )                              => NegLeftRule( f( subProof ), subProof.conclusion( index ) )
      case NegRightRule( subProof, index )                             => NegRightRule( f( subProof ), subProof.conclusion( index ) )
      case AndLeftRule( subProof, index1, index2 )                     => AndLeftRule( f( subProof ), subProof.conclusion( index1 ), subProof.conclusion( index2 ) )
      case AndRightRule( leftSubProof, index1, rightSubProof, index2 ) => AndRightRule( f( leftSubProof ), leftSubProof.conclusion( index1 ), f( rightSubProof ), rightSubProof.conclusion( index2 ) )
      case OrLeftRule( leftSubProof, index1, rightSubProof, index2 )   => OrLeftRule( f( leftSubProof ), leftSubProof.conclusion( index1 ), f( rightSubProof ), rightSubProof.conclusion( index2 ) )
      case OrRightRule( subProof, index1, index2 )                     => OrRightRule( f( subProof ), subProof.conclusion( index1 ), subProof.conclusion( index2 ) )
      case ImpLeftRule( leftSubProof, index1, rightSubProof, index2 )  => ImpLeftRule( f( leftSubProof ), leftSubProof.conclusion( index1 ), f( rightSubProof ), rightSubProof.conclusion( index2 ) )
      case ImpRightRule( subProof, index1, index2 )                    => ImpRightRule( f( subProof ), subProof.conclusion( index1 ), subProof.conclusion( index2 ) )
      case ForallLeftRule( subProof, _, a, term, v )                   => ForallLeftRule( f( subProof ), All( v, a ), term )
      case ForallRightRule( subProof, index, ev, qv )                  => ForallRightRule( f( subProof ), All( qv, Substitution( ev, qv )( subProof.conclusion( index ) ) ), ev )
      case ExistsLeftRule( subProof, index, ev, qv )                   => ExistsLeftRule( f( subProof ), Ex( qv, Substitution( ev, qv )( subProof.conclusion( index ) ) ), ev )
      case ExistsRightRule( subProof, _, a, term, v )                  => ExistsRightRule( f( subProof ), Ex( v, a ), term )
      case EqualityLeftRule( subProof, eq, index, pos )                => EqualityLeftRule( f( subProof ), subProof.conclusion( eq ), subProof.conclusion( index ), pos )
      case EqualityRightRule( subProof, eq, index, pos )               => EqualityRightRule( f( subProof ), subProof.conclusion( eq ), subProof.conclusion( index ), pos )
      case DefinitionLeftRule( subProof, index, main )                 => DefinitionLeftRule( f( subProof ), subProof.conclusion( index ), main )
      case DefinitionRightRule( subProof, index, main )                => DefinitionRightRule( f( subProof ), subProof.conclusion( index ), main )
      case _ =>
        throw new Exception( "Unmatched LK rule: " + p + ". Could not replace sub goal." )
    }

    val newSegment = f( proofSegment )

    new ProofState( initSequent, currentGoalIndex, newSegment )
  }
}

/**
 * Defines the case class open assumption which considers an arbitrary labelled sequence an axiom.
 * @param s
 */
case class OpenAssumption( s: Sequent[( HOLFormula, String )] ) extends InitialSequent {
  override def conclusion = s map { labelledFormula => labelledFormula._1 }
}

trait Tactical {
  /**
   *
   * @param proofState
   * @return
   */
  def apply( proofState: ProofState ): Option[ProofState]
}

trait Tactic extends Tactical {
  /**
   *
   * @param goal
   * @return
   */
  def apply( goal: OpenAssumption ): Option[LKProof]

  /**
   *
   * @param proofState
   * @return
   */
  override def apply( proofState: ProofState ): Option[ProofState] = {
    val Some( goal ) = proofState.getSubGoal( proofState.currentGoalIndex )
    val Some( proofSegment ) = this( goal )
    val newState = proofState.replaceSubGoal( proofState.currentGoalIndex, proofSegment )
    Some( newState )
  }
}

case class OrRightTactic( val requiredLabel: Option[String] = None ) extends Tactic {

  /**
   *
   * @param goal
   */
  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = this.requiredLabel match {
      case None =>
        for ( ( ( Or( _, _ ), _ ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index

      case Some( label ) =>
        for ( ( ( Or( _, _ ), `label` ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index
    }

    assert( !indices.isEmpty, "No matching formula found (Or)." )

    // Select some formula index!
    val i = indices.head

    // Extract LHS/RHS
    val ( Or( lhs, rhs ), existingLabel ) = goalSequent( i )

    // New goal with lhs, rhs instead of Or(lhs, rhs) in succedent
    val newGoal = goalSequent.delete( i ) :+ ( lhs, existingLabel + "_1" ) :+ ( rhs, existingLabel + "_2" )

    // Indices of lhs and rhs
    val lhsIndex = Suc( newGoal.succedent.length - 2 )
    val rhsIndex = lhsIndex + 1

    val premise = OpenAssumption( newGoal )

    Some( OrRightRule( premise, lhsIndex, rhsIndex ) )
  }

}

case class ImpRightTactic( val requiredLabel: Option[String] = None ) extends Tactic {

  /**
   *
   * @param goal
   */
  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = this.requiredLabel match {
      case None =>
        for ( ( ( Imp( _, _ ), _ ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index

      case Some( label ) =>
        for ( ( ( Imp( _, _ ), `label` ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index
    }

    assert( !indices.isEmpty, "No matching formula found (Imp)." )

    // Select some formula index!
    val i = indices.head

    // Extract LHS/RHS
    val ( Imp( lhs, rhs ), existingLabel ) = goalSequent( i )

    // New goal with lhs, rhs instead of Or(lhs, rhs) in succedent
    val newGoal = goalSequent.delete( i ).+:( lhs, existingLabel + "_1" ) :+ ( rhs, existingLabel + "_2" )

    // Indices of lhs and rhs
    val lhsIndex = Ant( 0 )
    val rhsIndex = Suc( newGoal.succedent.length - 1 )

    val premise = OpenAssumption( newGoal )

    Some( ImpRightRule( premise, lhsIndex, rhsIndex ) )
  }

}

case class ExistsLeftTactic( val eigenVariable: Var, val requiredLabel: Option[String] = None ) extends Tactic {

  /**
   *
   * @param goal
   */
  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = this.requiredLabel match {
      case None =>
        for ( ( ( Ex( _, _ ), _ ), index ) <- goalSequent.zipWithIndex.antecedent )
          yield index

      case Some( label ) =>
        for ( ( ( Ex( _, _ ), `label` ), index ) <- goalSequent.zipWithIndex.antecedent )
          yield index
    }

    assert( !indices.isEmpty, "No matching formula found (Ex)." )

    // Select some formula index!
    val i = indices.head

    val ( quantifiedFormula, existingLabel ) = goalSequent( i )
    val Ex( v, fm ) = quantifiedFormula

    val auxFormula = Substitution( v, eigenVariable )( fm )

    // New goal with instance of fm instead of Exi(v, fm)
    val newGoal = goalSequent.delete( i ).+:( auxFormula, existingLabel )

    val premise = OpenAssumption( newGoal )

    Some( ExistsLeftRule( premise, quantifiedFormula ) )
  }

}

case class ExistsRightTactic( val term: LambdaExpression, val requiredLabel: Option[String] = None ) extends Tactic {

  /**
   *
   * @param goal
   */
  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = this.requiredLabel match {
      case None =>
        for ( ( ( Ex( _, _ ), _ ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index

      case Some( label ) =>
        for ( ( ( Ex( _, _ ), `label` ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index
    }

    assert( !indices.isEmpty, "No matching formula found (Ex)." )

    // Select some formula index!
    val i = indices.head

    val ( quantifiedFormula, existingLabel ) = goalSequent( i )
    val Ex( v, fm ) = quantifiedFormula

    val auxFormula = Substitution( v, term )( fm )

    val newGoal = goalSequent.insertAt( i, ( auxFormula, existingLabel + "_" + term ) )

    val premise = OpenAssumption( newGoal )

    val auxProofSegment = ExistsRightRule( premise, quantifiedFormula, term )

    Some( ContractionRightRule( auxProofSegment, quantifiedFormula ) )
  }
}

/**
 * Tactic for "ForallLeftRule"
 */
case class ForallLeftTactic( term: LambdaExpression, val requiredLabel: Option[String] = None ) extends Tactic {

  /**
   *
   * @param goal
   */
  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = this.requiredLabel match {
      case None =>
        for ( ( ( All( _, _ ), _ ), index ) <- goalSequent.zipWithIndex.antecedent )
          yield index

      case Some( label ) =>
        for ( ( ( All( _, _ ), `label` ), index ) <- goalSequent.zipWithIndex.antecedent )
          yield index
    }

    assert( !indices.isEmpty, "No matching formula found (All)." )

    // Select some formula index!
    val i = indices.head

    val ( quantifiedFormula, existingLabel ) = goalSequent( i )
    val All( v, fm ) = quantifiedFormula

    val auxFormula = Substitution( v, term )( fm )

    val newGoal = goalSequent.insertAt( i + 1, ( auxFormula, existingLabel + "_" + term ) )

    val premise = OpenAssumption( newGoal )

    val auxProofSegment = ForallLeftRule( premise, quantifiedFormula, term )

    Some( ContractionLeftRule( auxProofSegment, quantifiedFormula ) )
  }

}

/**
 * Tactic for "ForallRightRule"
 */
case class ForallRightTactic( val requiredLabel: Option[String] = None ) extends Tactic {

  /**
   *
   * @param goal
   */
  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    val indices = this.requiredLabel match {
      case None =>
        for ( ( ( All( _, _ ), _ ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index

      case Some( label ) =>
        for ( ( ( All( _, _ ), `label` ), index ) <- goalSequent.zipWithIndex.succedent )
          yield index
    }

    ???
  }

}