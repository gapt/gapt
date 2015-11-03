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
  var proofSegment: LKProof = OpenAssumption( initGoal )

  private def getSubGoal( i: Int ): HOLSequent = {
    null
  }

  def displaySubGoal( i: Int ): String = {
    val sg = getSubGoal( i )

    "Some string " + sg
  }

  def replaceSubGoal( i: Int ): Unit = {
    val sg = getSubGoal( i )

    // replaces sub goal i
    // modifies the state
  }
}

/**
 *
 * @param S
 */
case class OpenAssumption( S: HOLSequent ) extends InitialSequent {
  override def endSequent = S
}

/**
 *
 */
abstract class Tactic {
  def apply( goal: HOLSequent ): LKProof
}

/**
 *
 */
object OrRightTactic extends Tactic {
  def apply( goal: HOLSequent ) = {

    val ms = ListBuffer[( Int, HOLFormula )]()

    for ( i <- 0 until goal.succedent.length-1 ) {
      goal.succedent( i ) match {
        case Or( _, _ ) => ms += ( ( i, goal.succedent( i ) ) )
      }
    }

    val ml = ms.toList

    // Select some formula!
    val i = ml.head._1
    val ( lhs, rhs ) = Or.unapply( ml.head._2 ) match {
      case Some( ( a, b ) ) => ( a, b )
      case None             => throw new RuntimeException( "Could not extract arguments from formula." )
    }

    goal.replaceAt( Suc( i ), lhs )
    goal.insertAt( Suc( i + 1 ), rhs )

    println( goal )

    null
  }
}