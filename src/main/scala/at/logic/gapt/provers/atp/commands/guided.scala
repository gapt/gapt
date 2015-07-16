
package at.logic.gapt.provers.atp.commands.guided

/**
 * this file contains command for a guided search using ids for clauses,as for example when parsing the output of theorem provers and using the rules from there
 */

import at.logic.gapt.proofs.resolution._
import at.logic.gapt.proofs.resolution.robinson.{ InitialClause }
import at.logic.gapt.proofs.lk.base.HOLSequent
import at.logic.gapt.proofs.occurrences._
import at.logic.gapt.expr._
import at.logic.gapt.provers.atp.Definitions._
import at.logic.gapt.provers.atp.commands.base.DataCommand
import scala.collection.mutable.Map

case class GetGuidedClausesCommand( parentIds: Iterable[String] ) extends DataCommand[OccClause] {
  def apply( state: State, data: Any ) = {
    //println("GetGuidedClausesCommand")
    val guidedMap = state( "gmap" ).asInstanceOf[Map[String, ResolutionProof[OccClause]]]
    //println("gclauses: " + parentIds.map(guidedMap(_).root))
    List( ( state, parentIds.map( guidedMap( _ ) ) ) )
  }
  override def toString = "GetGuidedClausesCommand(" + parentIds + ")"
}

case class GetGuidedClausesLiteralsPositions( ls: Iterable[Tuple3[String, Int, Iterable[Int]]] ) extends DataCommand[OccClause] {
  def apply( state: State, data: Any ) = {
    //println("GetGuidedClausesLiteralsPositions")
    val guidedMap = state( "gmap" ).asInstanceOf[Map[String, ResolutionProof[OccClause]]]
    List( ( state, ls.map( x => {
      val p = guidedMap( x._1 )
      ( p, p.root.literals( x._2 ), x._3 )
    } ) ) )
  }
  override def toString = "GetGuidedClausesLiteralsPositions(" + ls + ")"
}

case class GetGuidedClausesLiterals( ls: Iterable[Tuple2[String, Int]] ) extends DataCommand[OccClause] {
  def apply( state: State, data: Any ) = {
    //println("GetGuidedClausesLiterals")
    val guidedMap = state( "gmap" ).asInstanceOf[Map[String, ResolutionProof[OccClause]]]
    List( ( state, ls.map( x => {
      val p = guidedMap( x._1 )
      ( p, p.root.literals( x._2 ) )
    } ) ) )
  }
  override def toString = "GetGuidedClausesLiterals(" + ls + ")"
}

case class AddGuidedInitialClauseCommand( id: String, cls: Seq[FOLFormula] ) extends DataCommand[OccClause] {
  def apply( state: State, data: Any ) = {
    //println("AddGuidedInitialClauseCommand")
    val p = InitialClause( cls )( defaultFormulaOccurrenceFactory )
    val guidedMap = ( if ( state.isDefinedAt( "gmap" ) ) state( "gmap" ).asInstanceOf[Map[String, ResolutionProof[OccClause]]]
    else {
      val ret = Map[String, ResolutionProof[OccClause]]()
      state += new Tuple2( "gmap", ret )
      ret
    } )
    guidedMap += ( ( id, p ) )
    List( ( state, p ) )
  }
  override def toString = "AddGuidedInitialClauseCommand(" + id + ", " + cls + ")"
}

case class AddGuidedClausesCommand( ids: Iterable[String] ) extends DataCommand[OccClause] {
  def apply( state: State, data: Any ) = {
    //println("AddGuidedClausesCommand")
    val clauses = data.asInstanceOf[Iterable[ResolutionProof[OccClause]]]
    val guidedMap = ( if ( state.isDefinedAt( "gmap" ) ) state( "gmap" ).asInstanceOf[Map[String, ResolutionProof[OccClause]]]
    else {
      val ret = Map[String, ResolutionProof[OccClause]]()
      state += new Tuple2( "gmap", ret )
      ret
    } )
    clauses.zip( ids ).foreach( p => guidedMap += ( ( p._2, p._1 ) ) )
    List( ( state, clauses ) )
  }
  override def toString = "AddGuidedClausesCommand(" + ids + ")"
}

// we add a clause which might be a variant of that we look for.
case class AddGuidedResolventCommand( id: String ) extends DataCommand[OccClause] {
  def apply( state: State, data: Any ) = {
    //println("AddGuidedResolventCommand")
    val p = data.asInstanceOf[ResolutionProof[OccClause]]
    val guidedMap = ( if ( state.isDefinedAt( "gmap" ) ) state( "gmap" ).asInstanceOf[Map[String, ResolutionProof[OccClause]]]
    else {
      val ret = Map[String, ResolutionProof[OccClause]]()
      state += new Tuple2( "gmap", ret )
      ret
    } )
    guidedMap += ( ( id, p ) )
    //println("res: " + id + " - " + p.root)
    List( ( state, p ) )
  }
  override def toString = "AddGuidedResolventCommand(" + id + ")"
}

case object IsGuidedNotFoundCommand extends DataCommand[OccClause] {
  def apply( state: State, data: Any ) = {
    //println("IsGuidedNotFoundCommand")
    if ( !state.isDefinedAt( "guided_target_found" ) )
      List( ( state, data ) )
    else
      List()
  }
  override def toString = "IsGuidedNotFoundCommand()"
}

case object SetGuidedFoundCommand extends DataCommand[OccClause] {
  def apply( state: State, data: Any ) = {
    //println("SetGuidedFoundCommand")
    state += ( ( "guided_target_found", true ) )
    List( ( state, data ) )
  }
  override def toString = "SetGuidedFoundCommand()"
}

