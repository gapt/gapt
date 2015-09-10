
package at.logic.gapt.provers.atp.commands.refinements.simple

import at.logic.gapt.proofs.lk.base.{ OccSequent, RichOccSequent }
import at.logic.gapt.proofs.resolutionOld.ResolutionProof
import at.logic.gapt.provers.atp.commands.base.InitialCommand
import at.logic.gapt.provers.atp.commands.refinements.base.{ Refinement, RefinementID }
import at.logic.gapt.provers.atp.Definitions._
import at.logic.gapt.utils.ds.PublishingBuffer
import at.logic.gapt.utils.logging.Logger
import collection.mutable.ListBuffer

// the command
case class SimpleRefinementGetCommand[V <: OccSequent]() extends InitialCommand[V] with Logger {
  def apply( state: State ) = {
    val refinement =
      if ( state.isDefinedAt( RefinementID() ) ) state( RefinementID() ).asInstanceOf[SimpleRefinement[V]]
      else {
        val ref = new SimpleRefinement( state( "clauses" ).asInstanceOf[PublishingBuffer[ResolutionProof[V]]] )
        state += new Tuple2( RefinementID(), ref )
        ref
      }
    refinement.getNext match {
      case None      => List()
      case Some( p ) => debug( p toString ); List( ( state, p ) )
    }
  }

  override def toString = "SimpleRefinementGetCommand()"

}

private[refinements] class SimpleRefinement[V <: OccSequent]( clauses: PublishingBuffer[ResolutionProof[V]] ) extends Refinement[V]( clauses ) {
  val pairs = new ListBuffer[Tuple2[ResolutionProof[V], ResolutionProof[V]]] // all pairs of possible two clauses
  insertClauses
  def getNext: Option[Tuple2[ResolutionProof[V], ResolutionProof[V]]] = if ( isEmpty ) None else Some( pairs.remove( 0 ) )

  private def insertClauses = {
    val tmp = clauses.toList
    pairs ++= ( for {
      ( a, i ) <- tmp.zip( tmp.indices )
      j <- tmp.indices
      if ( j > i )
    } yield ( a, clauses( j ) ) )
  }
  protected def addClause( s: ResolutionProof[V] ) = {
    pairs ++= clauses.map( a => ( s, a ) )
  }
  protected def removeClause( s: ResolutionProof[V] ) = {
    pairs.filter( x => ( x._1.root syntacticMultisetEquals s.root ) || ( x._2.root syntacticMultisetEquals s.root ) ).foreach( x => pairs -= x )
  }
  def isEmpty: Boolean = pairs.isEmpty

  override def toString = "SimpleRefinement(" + clauses + ")"

}

