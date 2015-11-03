package at.logic.gapt.proofs

import at.logic.gapt.expr.{ HOLFormula, Or }
import at.logic.gapt.proofs.lkNew.{ OrRightRule, InitialSequent, LKProof }

import scala.collection.mutable.ListBuffer

/**
 *
 * @param initGoal
 */
class ProofState( initGoal: HOLSequent ) {
  var goal: HOLSequent = initGoal
  var subGoals: List[HOLSequent] = List( this.goal )
  var proofSegment: LKProof = OpenAssumption( initGoal, "label" )

  def getSubGoal( i: Int ): Option[HOLSequent] = {
    ???
  }

  private def getSubGoalInternal( i: Int ): HOLSequent = {
    ???
  }

  def displaySubGoal( i: Int ): String = {
    val sg = getSubGoal( i )

    "Some string " + sg
  }

  private def replaceSubGoal( i: Int, segment: LKProof ): ProofState = {
    val sg = getSubGoal( i )

    // replaces sub goal i in a new proof state

    ???
  }
}

/**
 *
 * @param S
 */
case class OpenAssumption( S: HOLSequent, label: String ) extends InitialSequent {
  override def conclusion = S
}

/**
 *
 */
abstract class Tactic {
  def rule( goal: HOLSequent ): LKProof

  final def apply( goal: HOLSequent, p: ProofState ): Option[ProofState] = {

    try {
      val segment = rule( goal )

      println( segment )

      ???
    } catch {
      case ex: Exception =>
    }

    None
  }
}
/**
 *
 */
abstract class Tactical {
  def rule( goal: HOLSequent ): LKProof

  final def apply( p: ProofState ): Option[ProofState] = {

    //

    None
  }
}

/**
 *
 */
object OrRightTactic extends Tactic {

  def rule( goal: HOLSequent ) = {
    val indices =
      for ( ( Or( _, _ ), index ) <- goal.zipWithIndex.succedent )
        yield index

    if ( indices.isEmpty )
      throw new Exception( "No matching formula found (Or)." )

    // Select some formula!
    val i = indices.head

    // Extract LHS/RHS
    val Or( lhs, rhs ) = goal( i )

    // New goal with lhs, rhs instead of Or(lhs, rhs) in succedent
    val newGoal = goal.delete( i ) :+ lhs :+ rhs

    // Indices of lhs and rhs
    val lhsIndex = Suc( newGoal.succedent.length - 2 )
    val rhsIndex = lhsIndex + 1

    val premise = OpenAssumption( newGoal, "label" )

    OrRightRule( premise, lhsIndex, rhsIndex )
  }
}