
package at.logic.gapt.provers.atp.commands.sequents

import at.logic.gapt.proofs.lk.subsumption.managers._
import at.logic.gapt.proofs.lk.subsumption.{ StillmanSubsumptionAlgorithmFOL, SubsumptionAlgorithm }
import at.logic.gapt.expr.fol.FOLMatchingAlgorithm
import at.logic.gapt.proofs.lk.base._
import at.logic.gapt.proofs.resolution.{ ResolutionProof, OccClause }
import at.logic.gapt.expr._
import at.logic.gapt.provers.atp.commands.base.{ ResultCommand, DataCommand }
import at.logic.gapt.provers.atp.Definitions._
import at.logic.gapt.utils.ds.{ Add, Remove, PublishingBufferEvent, PublishingBuffer }
import at.logic.gapt.utils.logging.Logger
import at.logic.gapt.utils.patterns.listeners.ListenerManager

abstract class SetSequentsCommand[V <: OccSequent]( val clauses: Iterable[HOLSequent] ) extends DataCommand[V]

// set the target clause, i.e. the empty clause normally
case class SetTargetClause[V <: OccSequent]( val clause: HOLSequent ) extends DataCommand[V] with Logger {
  def apply( state: State, data: Any ) = {
    debug( s"targetClause <- $clause" )
    List( ( state += new Tuple2( "targetClause", clause ), data ) )
  }
}

// tests whether the clauses list contains the target clause
case class SearchForEmptyClauseCommand[V <: OccSequent]() extends ResultCommand[V] {
  def apply( state: State, data: Any ) = {
    val target = state( "targetClause" ).asInstanceOf[HOLSequent]
    state( "clauses" ).asInstanceOf[PublishingBuffer[ResolutionProof[V]]].find( x => fvarInvariantMSEquality( x.root, target ) )
  }
}

case class InsertResolventCommand[V <: OccSequent]() extends DataCommand[V] {
  def apply( state: State, data: Any ) = {
    ( if ( state.isDefinedAt( "clauses" ) ) state( "clauses" ).asInstanceOf[PublishingBuffer[ResolutionProof[V]]]
    else {
      val pb = new PublishingBuffer[ResolutionProof[V]]
      state += new Tuple2( "clauses", pb )
      pb
    } ) += data.asInstanceOf[ResolutionProof[V]]
    List( ( state, data ) )
  }

  override def toString = "InsertResolventCommand()"

}

// deterministically trying to match all indices (it is deterministic as it does not change the state of the different cases)
case class ApplyOnAllPolarizedLiteralPairsCommand[V <: OccSequent]() extends DataCommand[V] with Logger {
  def apply( state: State, data: Any ) = {
    val p = data.asInstanceOf[Tuple2[ResolutionProof[V], ResolutionProof[V]]]
    debug( p toString )
    ( for ( i <- p._1.root.antecedent; j <- p._2.root.succedent ) yield ( state, List( ( p._2, ( j, true ) ), ( p._1, ( i, false ) ) ) ) ) ++
      ( for ( i <- p._1.root.succedent; j <- p._2.root.antecedent ) yield ( state, List( ( p._1, ( i, true ) ), ( p._2, ( j, false ) ) ) ) )
  }
}

case class RefutationReachedCommand[V <: OccSequent]() extends ResultCommand[V] with Logger {
  def apply( state: State, data: Any ) = {
    val target = state( "targetClause" ).asInstanceOf[HOLSequent]
    val d = data.asInstanceOf[ResolutionProof[V]]
    debug( d.root toString )
    if ( fvarInvariantMSEquality( d.root, target ) ) {
      Some( d )
    } else {
      None
    }
  }

  override def toString = "RefutationReachedCommand"
}

case class SubsumedTargedSetFromClauseSetCommand[V <: OccSequent]() extends ResultCommand[V] {
  def apply( state: State, data: Any ) = {
    val target = state( "targetClause" ).asInstanceOf[HOLSequent]
    val clauses = state( "clauses" ).asInstanceOf[Traversable[ResolutionProof[V]]]
    val alg = StillmanSubsumptionAlgorithmFOL
    val res = clauses.find( c => alg.subsumes( c.root.toHOLSequent, target ) )
    res
  }
}

//checks whether the resolvent is subsumed
case class SubsumedTargedReachedCommand[V <: OccSequent]() extends ResultCommand[V] {
  def apply( state: State, data: Any ) = {
    val target = state( "targetClause" ).asInstanceOf[HOLSequent]
    val d = data.asInstanceOf[ResolutionProof[V]]
    if ( firstSubsumesSecond( d.root.toHOLSequent, target ) ) Some( d )
    else None
  }
  def firstSubsumesSecond( s1: HOLSequent, s2: HOLSequent ): Boolean = {
    val alg = StillmanSubsumptionAlgorithmFOL
    alg.subsumes( s1, s2 )
  }
}

//cvetan - kommutativity of the equality
object fvarInvariantMSEqualityEQ {
  val dnLine = sys.props( "line.separator" ) + sys.props( "line.separator" )
  def apply[V <: OccSequent]( c1: V, f2: HOLSequent ): Boolean = {
    if ( f2.succedent.length == 0 )
      return false
    f2.succedent.head match {
      case Eq( a, b ) => {
        println( dnLine + "Vutre sum !" + dnLine )
        val f3 = HOLSequent( f2.antecedent, Eq( b, a ) +: f2.succedent.tail )
        return fvarInvariantMSEquality( c1, f3 )
      }
      case _ => return false
    }
  }
}

// tests for multiset equality while ignoring the names of the free variables
// FIXME: this is the only command that uses HOL... why is this mixed??
object fvarInvariantMSEquality {
  def apply[V <: OccSequent]( c1: V, f2: HOLSequent ): Boolean = {
    val f1 = ( c1.antecedent.map( _.formula ), c1.succedent.map( _.formula ) )
    val HOLSequent( neg, pos ) = f2
    // we get all free variables from f2 and try to systematically replace those in f1
    val set1 = ( f1._1 ++ f1._2 ).flatMap( subTerms( _ ) ).filter( e => e match { case f: Var => true; case _ => false } )
    val set2 = ( f2.antecedent ++ f2.succedent ).flatMap( subTerms( _ ) ).filter( e => e match { case f: Var => true; case _ => false } )
    if ( set1.size != set2.size ) List[HOLSequent]() // they cannot be equal
    // create all possible substitutions
    ( for ( s <- set1.toList.permutations.map( _.zip( set2 ) ).map( x => Substitution( x.asInstanceOf[List[Tuple2[Var, LambdaExpression]]] ) ) )
      yield ( f1._1.map( s( _ ).asInstanceOf[HOLFormula] ), f1._2.map( s( _ ).asInstanceOf[HOLFormula] ) ) ).toList.exists( cls => {
      neg.diff( cls._1 ).isEmpty && pos.diff( cls._2 ).isEmpty && cls._1.diff( neg ).isEmpty && cls._2.diff( pos ).isEmpty
    } )
  }
}

case class IfNotExistCommand[V <: OccSequent]() extends DataCommand[V] {
  def apply( state: State, data: Any ) = {
    val buffer = state( "clauses" ).asInstanceOf[PublishingBuffer[ResolutionProof[V]]]
    val res = data.asInstanceOf[ResolutionProof[V]]
    if ( !buffer.exists( x => x.root == res.root ) ) List( ( state, data ) ) else List()
  }
}

abstract class SimpleSubsumptionCommand[V <: OccSequent]( val alg: SubsumptionAlgorithm ) extends DataCommand[V] {
  protected def getManager( state: State ): SubsumptionManager = {
    if ( state.isDefinedAt( "simpleSubsumManager" ) ) state( "simpleSubsumManager" ).asInstanceOf[SubsumptionManager]
    else {
      val buffer = state( "clauses" ).asInstanceOf[PublishingBuffer[ResolutionProof[V]]]
      // set a listener that will listen to the buffer and fire an event (to the subsumption manager) when sequents are added or removed
      val lis = new ListenerManager[SubsumptionDSEvent] {
        buffer.addListener( ( x: PublishingBufferEvent[ResolutionProof[V]] ) => x.ar match {
          case Add    => fireEvent( SubsumptionDSEvent( SAdd, x.elem.root.toHOLSequent ) )
          case Remove => fireEvent( SubsumptionDSEvent( SRemove, x.elem.root.toHOLSequent ) )
        } )
      }
      val man = new SimpleManager( lis, alg, () => buffer.iterator.map( _.root.toHOLSequent ), f => buffer.exists( p => f( p.root.toHOLSequent ) ), s => { buffer.filterNot( _.root.toHOLSequent == s ); () } )
      state( "simpleSubsumManager" ) = man
      man
    }
  }
  override def toString = "SimpleSubsumptionCommand(" + alg.getClass + ")"
}

case class SimpleForwardSubsumptionCommand[V <: OccSequent]( a: SubsumptionAlgorithm ) extends SimpleSubsumptionCommand[V]( a ) with Logger {
  def apply( state: State, data: Any ) = {
    val manager = getManager( state )
    val res = data.asInstanceOf[ResolutionProof[V]]
    val res1 = res.root.toHOLSequent
    val isSubsumed = manager forwardSubsumption res1
    debug( s"${if ( isSubsumed ) "subsumed" else "NOT subsumed"}: $res1" )
    if ( isSubsumed ) List() else List( ( state, data ) )
  }
  override def toString = "SimpleForwardSubsumptionCommand(" + a.getClass + ")"
}

case class SimpleBackwardSubsumptionCommand[V <: OccSequent]( a: SubsumptionAlgorithm ) extends SimpleSubsumptionCommand[V]( a ) with Logger {
  def apply( state: State, data: Any ) = {
    val manager = getManager( state )
    val res = data.asInstanceOf[ResolutionProof[V]]
    val res1 = res.root.toHOLSequent
    debug( res1 toString )
    manager.backwardSubsumption( res1 )
    List( ( state, data ) )
  }
  override def toString = "SimpleBackwardSubsumptionCommand(" + a.getClass + ")"
}
