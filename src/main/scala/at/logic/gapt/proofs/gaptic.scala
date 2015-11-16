package at.logic.gapt.proofs

import at.logic.gapt.expr._
import at.logic.gapt.proofs.lkNew._

/**
 * Immutable object defining the current state of the proof in the tactics language.
 * @param initFormula
 */
class ProofState( val initFormula: HOLFormula, val currentGoalIndex: Int, val proofSegment: LKProof, val theoremName: String ) {
  val subGoals: Seq[OpenAssumption] =
    for ( OpenAssumption( s ) <- proofSegment.postOrder )
      yield OpenAssumption( s )

  require( currentGoalIndex >= 0 && currentGoalIndex <= subGoals.length )

  /**
   * Constructor with name of theorem and initial formula.
   * @param initFormula
   * @param initFormulaName
   * @param theoremName
   * @return
   */
  def this( initFormula: HOLFormula, theoremName: String, initFormulaName: String ) = this( initFormula, 0, OpenAssumption( Sequent( Seq(), Seq( ( initFormula, initFormulaName ) ) ) ), theoremName )

  /**
   * Constructor with name of theorem, and default name for initial formula.
   * @param initFormula
   * @param theoremName
   * @return
   */
  def this( initFormula: HOLFormula, theoremName: String ) = this( initFormula, theoremName, "x" )

  /**
   * Constructor with default name for theorem and initial formula.
   * @param initFormula
   * @return
   */
  def this( initFormula: HOLFormula ) = this( initFormula, "thm" )

  /**
   * Returns the sub goal at a given index if it exists.
   * @param i
   * @return
   */
  def getSubGoal( i: Int ): Option[OpenAssumption] = try {
    val sg = getSubGoalInternal( i )
    Some( sg )
  } catch {
    case ex: Exception => None
  }

  /**
   * Returns sub goal at a given index. Throws an exception on fail.
   * @param i
   * @return
   */
  private def getSubGoalInternal( i: Int ): OpenAssumption = {
    assert( i >= 0 && i < subGoals.length, "Sub goal index out of bounds" )

    subGoals( i )
  }

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

    new ProofState( initFormula, currentGoalIndex, newSegment, theoremName )
  }
}

/**
 * Defines the case class open assumption which considers an arbitrary labelled sequence an axiom.
 * @param s
 */
case class OpenAssumption( s: Sequent[( HOLFormula, String )] ) extends InitialSequent {
  override def conclusion = s.map( f => {
    val ( h, _ ) = f;
    h
  } )
}

/**
 * Trait for tactic applied once to a sub goal.
 */
abstract class Tactic

/**
 * Tactics that takes no additional arguments
 */
abstract class BasicTactic extends Tactic {
  /**
   * Abstract method to be implemented by any tactic returning the resulting proof segment after application.
   * @param o
   * @param label
   * @return
   */
  def rule( o: OpenAssumption, label: Option[String] ): LKProof

  /**
   * Defines the call pattern that is to be used by any subclass on application of tactic.
   * @param goalIndex
   * @param p
   * @return
   */
  final def apply( goalIndex: Int, p: ProofState, label: Option[String] = None ): Option[ProofState] = try {
    val o = p.subGoals( goalIndex )
    val segment = rule( o, label )

    Some( p.replaceSubGoal( goalIndex, segment ) )
  } catch {
    case lkc: LKRuleCreationException => throw lkc
    case ex: Exception                => None
  }

  /**
   * Alternative call pattern for tactic.
   * @param p
   * @return
   */
  final def apply( p: ProofState ): Option[ProofState] = apply( p.currentGoalIndex, p )
}

/**
 * Tactics that require an additional variable for instantiation or quantification
 */
abstract class InstantiationTactic extends Tactic {
  /**
   * Abstract method to be implemented by any tactic returning the resulting proof segment after application.
   * @param o
   * @param x
   * @param label
   * @return
   */
  def rule( o: OpenAssumption, x: Either[Var, LambdaExpression], label: Option[String] ): LKProof

  /**
   * Defines the call pattern that is to be used by any subclass on application of tactic.
   * @param goalIndex
   * @param p
   * @param x
   * @param label
   * @return
   */
  final def apply( goalIndex: Int, p: ProofState, x: Either[Var, LambdaExpression], label: Option[String] = None ): Option[ProofState] = try {
    val o = p.subGoals( goalIndex )
    val segment = rule( o, x, label )

    Some( p.replaceSubGoal( goalIndex, segment ) )
  } catch {
    case lkc: LKRuleCreationException => throw lkc
    case ex: Exception                => None
  }

  /**
   * Alternative call patterns for tactic.
   */

  final def apply( p: ProofState, eigenVariable: Var ): Option[ProofState] = apply( p.currentGoalIndex, p, Left( eigenVariable ) )

  final def apply( p: ProofState, eigenVariable: Var, label: String ): Option[ProofState] = apply( p.currentGoalIndex, p, Left( eigenVariable ), Some( label ) )

  final def apply( p: ProofState, term: LambdaExpression ): Option[ProofState] = apply( p.currentGoalIndex, p, Right( term ) )

  final def apply( p: ProofState, term: LambdaExpression, label: String ): Option[ProofState] = apply( p.currentGoalIndex, p, Right( term ), Some( label ) )
}

/**
 * Abstract class for tactical applying tactics arbitrarily to a proof state.
 */
abstract class Tactical {

  /**
   *
   * @param p
   * @return
   */
  final def apply( p: ProofState ): Option[ProofState] = {

    //

    None
  }
}

/**
 * Tactic for "OrRightRule"
 */
object OrRightTactic extends BasicTactic {

  /**
   *
   * @param o
   * @return
   */
  def rule( o: OpenAssumption, label: Option[String] ) = {
    val goal = o.s

    val indices = label match {
      case None =>
        for ( ( ( Or( _, _ ), _ ), index ) <- goal.zipWithIndex.succedent )
          yield index

      case _ =>
        for ( ( ( Or( _, _ ), label ), index ) <- goal.zipWithIndex.succedent )
          yield index
    }

    assert( !indices.isEmpty, "No matching formula found (Or)." )

    // Select some formula index!
    val i = indices.head

    // Extract LHS/RHS
    val ( Or( lhs, rhs ), existingLabel ) = goal( i )

    // New goal with lhs, rhs instead of Or(lhs, rhs) in succedent
    val newGoal = goal.delete( i ) :+ ( lhs, existingLabel + "_1" ) :+ ( rhs, existingLabel + "_2" )

    // Indices of lhs and rhs
    val lhsIndex = Suc( newGoal.succedent.length - 2 )
    val rhsIndex = lhsIndex + 1

    val premise = OpenAssumption( newGoal )

    OrRightRule( premise, lhsIndex, rhsIndex )
  }

}

/**
 * Tactic for "ImpRightRule"
 */
object ImpRightTactic extends BasicTactic {

  /**
   *
   * @param o
   * @return
   */
  def rule( o: OpenAssumption, label: Option[String] ) = {
    val goal = o.s

    val indices = label match {
      case None =>
        for ( ( ( Imp( _, _ ), _ ), index ) <- goal.zipWithIndex.succedent )
          yield index

      case _ =>
        for ( ( ( Imp( _, _ ), label ), index ) <- goal.zipWithIndex.succedent )
          yield index
    }

    assert( !indices.isEmpty, "No matching formula found (Imp)." )

    // Select some formula index!
    val i = indices.head

    // Extract LHS/RHS
    val ( Imp( lhs, rhs ), existingLabel ) = goal( i )

    // New goal with lhs, rhs instead of Or(lhs, rhs) in succedent
    val newGoal = goal.delete( i ).+:( lhs, existingLabel + "_1" ) :+ ( rhs, existingLabel + "_2" )

    // Indices of lhs and rhs
    val lhsIndex = Ant( 0 )
    val rhsIndex = Suc( newGoal.succedent.length - 1 )

    val premise = OpenAssumption( newGoal )

    ImpRightRule( premise, lhsIndex, rhsIndex )
  }

}

/**
 * Tactic for "ExistLeftRule"
 */
object ExistsLeftTactic extends InstantiationTactic {

  /**
   *
   * @param o
   * @return
   */
  def rule( o: OpenAssumption, x: Either[Var, LambdaExpression], label: Option[String] ) = {
    val goal = o.s

    val eigenVariable = x match {
      case Left( y ) => y
      case _         => throw new Exception( "Expected x to be of type Var" )
    }

    val indices = label match {
      case None =>
        for ( ( ( Ex( _, _ ), _ ), index ) <- goal.zipWithIndex.antecedent )
          yield index

      case _ =>
        for ( ( ( Ex( _, _ ), label ), index ) <- goal.zipWithIndex.antecedent )
          yield index
    }

    assert( !indices.isEmpty, "No matching formula found (Ex)." )

    // Select some formula index!
    val i = indices.head

    val ( quantifiedFormula, existingLabel ) = goal( i )
    val Ex( v, fm ) = quantifiedFormula

    val auxFormula = Substitution( v, eigenVariable )( fm )

    // New goal with instance of fm instead of Exi(v, fm)
    val newGoal = goal.delete( i ).+:( auxFormula, existingLabel )

    val premise = OpenAssumption( newGoal )

    ExistsLeftRule( premise, quantifiedFormula )
  }

}

/**
 * Tactic for "ExistsRightRule"
 */
object ExistsRightTactic extends InstantiationTactic {

  /**
   *
   * @param o
   * @return
   */
  def rule( o: OpenAssumption, x: Either[Var, LambdaExpression], label: Option[String] ) = {
    val goal = o.s

    val term = x match {
      case Right( y ) => y
      case _          => throw new Exception( "Expected x to be of type LambdaExpression" )
    }

    val indices = label match {
      case None =>
        for ( ( ( Ex( _, _ ), _ ), index ) <- goal.zipWithIndex.succedent )
          yield index

      case _ =>
        for ( ( ( Ex( _, _ ), label ), index ) <- goal.zipWithIndex.succedent )
          yield index
    }

    assert( !indices.isEmpty, "No matching formula found (Ex)." )

    // Select some formula index!
    val i = indices.head

    val ( quantifiedFormula, existingLabel ) = goal( i )
    val Ex( v, fm ) = quantifiedFormula

    val auxFormula = Substitution( v, term )( fm )

    val newGoal = goal.insertAt( i, ( auxFormula, existingLabel + "_" + term ) )

    val premise = OpenAssumption( newGoal )

    val auxProofSegment = ExistsRightRule( premise, quantifiedFormula, term )
    ContractionRightRule( auxProofSegment, quantifiedFormula )
  }
}

/**
 * Tactic for "ForallLeftRule"
 */
object ForallLeftTactic extends InstantiationTactic {

  /**
   *
   * @param o
   * @return
   */
  def rule( o: OpenAssumption, x: Either[Var, LambdaExpression], label: Option[String] ) = {
    val goal = o.s

    val term = x match {
      case Right( y ) => y
      case _          => throw new Exception( "Expected x to be of type LambdaExpression" )
    }

    val indices = label match {
      case None =>
        for ( ( ( All( _, _ ), _ ), index ) <- goal.zipWithIndex.antecedent )
          yield index

      case _ =>
        for ( ( ( All( _, _ ), label ), index ) <- goal.zipWithIndex.antecedent )
          yield index
    }

    assert( !indices.isEmpty, "No matching formula found (All)." )

    // Select some formula index!
    val i = indices.head

    val ( quantifiedFormula, existingLabel ) = goal( i )
    val All( v, fm ) = quantifiedFormula

    val auxFormula = Substitution( v, term )( fm )

    val newGoal = goal.insertAt( i + 1, ( auxFormula, existingLabel + "_" + term ) )

    val premise = OpenAssumption( newGoal )

    val auxProofSegment = ForallLeftRule( premise, quantifiedFormula, term )
    ContractionLeftRule( auxProofSegment, quantifiedFormula )
  }

}

/**
 * Tactic for "ForallRightRule"
 */
object ForallRightTactic extends InstantiationTactic {

  /**
   *
   * @param o
   * @return
   */
  def rule( o: OpenAssumption, x: Either[Var, LambdaExpression], label: Option[String] ) = {
    val goal = o.s

    ???
  }

}