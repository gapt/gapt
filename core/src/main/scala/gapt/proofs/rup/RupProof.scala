package gapt.proofs.rup
import java.util

import gapt.expr.Formula
import gapt.formats.dimacs.DIMACS
import gapt.proofs.DagProof
import gapt.proofs.lk.LKProof
import gapt.proofs.resolution.ResolutionProof
import gapt.proofs.rup.RupProof._
import org.sat4j.core.{ LiteralsUtils, Vec, VecInt }
import org.sat4j.minisat.constraints.MixedDataStructureDanielWL
import org.sat4j.minisat.constraints.cnf.{ OriginalBinaryClause, OriginalWLClause, UnitClause }
import org.sat4j.minisat.core.{ Constr, Propagatable }
import org.sat4j.specs.{ IConstr, UnitPropagationListener }

import scala.collection.mutable

/**
 * Simple forward RUP-to-resolution converter based on Sat4j's unit propagation code.
 *
 * Whenever a unit propagation is performed, we compute a resolution
 * proof of the assigned literal.  There two modes:
 *
 *  - At decision level 0, we add clauses for which we already have complete
 *  proofs (given as input proofs, or already derived via RUP).  The proofs
 *  we associate to the propagated literals have the corresponding unit
 *  clause as conclusion.
 *
 *  - At decision level 1, we want to derive a new clause via RUP.  Here, the
 *  conclusion of a proof associated with a propagated literal may also include
 *  literals from the derived clause.  As an optimization, we do store tautology
 *  proofs as null.
 */
private class Rup2Res extends UnitPropagationListener {
  val ds = new MixedDataStructureDanielWL
  ds.setUnitPropagationListener( this )
  val voc = ds.getVocabulary

  val trail = new VecInt
  val trailLim = new VecInt
  val proofs = new Vec[Res]
  var queueHead = 0
  var conflict: Option[Res] = None

  val constrProofs = new util.IdentityHashMap[IConstr, Res]()

  import LiteralsUtils._

  def decisionLevel: Int = trailLim.size()

  def assume(): Unit = {
    assert( trail.size() == queueHead )
    trailLim.push( trail.size() )
  }
  def cancel(): Unit = {
    while ( trail.size() > trailLim.last() ) {
      val p = trail.last()
      voc.unassign( p )
      voc.setReason( p, null )
      voc.setLevel( p, -1 )
      proofs.set( p, null )
      trail.pop()
    }
    queueHead = trail.size()
    conflict = None
    trailLim.pop()
  }

  def enqueue( p: Int ): Boolean = enqueue( p, null )
  def enqueue( p: Int, from: Constr ): Boolean = {
    // from == null  IFF  literal is from the clause to be derived

    if ( voc.isSatisfied( p ) ) return true

    val proofP = if ( from == null ) null else {
      var pp = constrProofs.get( from )
      for ( q <- pp.clause if q != toDimacs( p ) )
        proofs.get( toInternal( -q ) ) match {
          case null =>
          case proofQ =>
            pp = Res.Resolve.f( pp, proofQ, math.abs( q ) )
        }
      pp
    }

    if ( voc.isFalsified( p ) ) {
      conflict = Some( ( proofs.get( neg( p ) ), proofP ) match {
        case ( null, null )      => Res.Taut( math.abs( toDimacs( p ) ) )
        case ( null, _ )         => proofP
        case ( proofNotP, null ) => proofNotP
        case ( proofNotP, _ )    => Res.Resolve.f( proofNotP, proofP, math.abs( toDimacs( p ) ) )
      } )
      return false
    }

    voc.satisfies( p )
    voc.setLevel( p, decisionLevel )
    proofs.set( p, proofP )
    trail.push( p )
    true
  }
  def unset( p: Int ): Unit = throw new UnsupportedOperationException

  def propagate(): Boolean = {
    while ( queueHead < trail.size() ) {
      val p = trail.get( queueHead )
      queueHead += 1

      val watches = new Vec[Propagatable]
      voc.watches( p ).moveTo( watches )
      while ( !watches.isEmpty ) {
        val w = watches.last()
        watches.pop()
        if ( !w.propagate( this, p ) ) { // conflict
          while ( !watches.isEmpty ) {
            voc.watch( p, watches.last() )
            watches.pop()
          }
          queueHead = trail.size()
          return false
        }
      }
    }
    true
  }

  def getFromPool( dimacsVar: Int ): Int = {
    if ( 2 * math.abs( dimacsVar ) + 2 > proofs.size() )
      proofs.growTo( math.max( 2 * math.abs( dimacsVar ) + 2, 2 * proofs.size() ), null )

    voc.getFromPool( dimacsVar )
  }

  def addClause( p0: Res ): Boolean = {
    var p = p0
    if ( p.clause.exists( i => voc.isSatisfied( getFromPool( i ) ) ) ) return true
    for ( i <- p.clause; ii = getFromPool( i ) if voc.isFalsified( ii ) )
      p = Res.Resolve.f( proofs.get( neg( ii ) ), p, math.abs( i ) )

    if ( p.clause.isEmpty ) {
      conflict = Some( p )
      return false
    }
    val cls = new VecInt( p.clause.view.map( getFromPool ).toArray )
    val constr =
      if ( cls.size() == 1 )
        new UnitClause( cls.last() )
      else if ( cls.size() == 2 )
        OriginalBinaryClause.brandNewClause( this, voc, cls )
      else
        OriginalWLClause.brandNewClause( this, voc, cls )

    constrProofs.put( constr, p )

    if ( cls.size() == 1 ) enqueue( cls.last(), constr )

    propagate()
  }

  def deriveRup( cls: Clause ): Res = {
    assume()
    cls.forall( i =>
      enqueue( getFromPool( -i ) ) ) &&
      propagate()
    val Some( p ) = conflict
    cancel()
    require( p.clause subsetOf cls )
    addClause( p )
    p
  }
}

/** Reverse unit propagation proof. */
case class RupProof( lines: Vector[Line] ) {
  def maxVar: Int = ( 0 +: lines.view.flatMap( _.clause ) ).max

  def toResProofs: Vector[Res] = {
    val rup2res = new Rup2Res
    lines.map {
      case _ if rup2res.conflict.isDefined => rup2res.conflict.get
      case RupProof.Input( c ) =>
        val p = Res.Input( c )
        rup2res.addClause( p )
        p
      case RupProof.Rup( c ) => rup2res.deriveRup( c )
    }
  }

  def toRes: Res = RupProof( lines :+ RupProof.Rup( Set() ) ).toResProofs.last

  override def toString: String =
    lines.view.map {
      case RupProof.Input( cls ) => "I " + cls.mkString( " " ) + " 0"
      case RupProof.Rup( cls )   => cls.mkString( " " ) + " 0"
    }.mkString( "\n" )
}

object RupProof {
  type Clause = Set[Int]

  /** Inference in a [[RupProof]] */
  sealed trait Line {
    def clause: Clause
  }
  /** Input clause. */
  case class Input( clause: Clause ) extends Line
  /**
   * Clause derived from the previous ones via RUP.
   *
   * Given a set of clauses Γ and a clause C, then C has the property RUP
   * with regard to Γ iff Γ, ¬C can be refuted with only unit propagation.
   */
  case class Rup( clause: Clause ) extends Line

  def apply( cnf: DIMACS.CNF, p: DIMACS.DRUP ): RupProof = {
    import DIMACS._
    RupProof( Vector() ++
      cnf.view.map( cls => Input( cls.toSet ) ) ++
      p.view.collect { case DrupDerive( cls ) => Rup( cls.toSet ) } )
  }
}

/** Resolution proofs in DIMACS format. */
sealed trait Res extends DagProof[Res] {
  def clause: Clause

  def toResolution( atom: Int => Formula, input: Clause => ResolutionProof ): ResolutionProof = {
    import gapt.proofs.resolution._
    val memo = mutable.Map[Res, ResolutionProof]()
    def go( p: Res ): ResolutionProof =
      memo.getOrElseUpdate( p, Factor( p match {
        case Res.Taut( v )          => Taut( atom( v ) )
        case Res.Input( c )         => input( c )
        case Res.Resolve( a, b, v ) => Resolution( go( a ), go( b ), atom( v ) )
      } ) )
    go( this )
  }

  def toLK( atom: Int => Formula, input: Clause => LKProof ): LKProof = {
    import gapt.proofs.lk._
    val memo = mutable.Map[Res, LKProof]()
    def go( p: Res ): LKProof =
      memo.getOrElseUpdate( p, ContractionMacroRule( p match {
        case Res.Taut( v )          => LogicalAxiom( atom( v ) )
        case Res.Input( c )         => input( c )
        case Res.Resolve( a, b, v ) => CutRule( go( a ), go( b ), atom( v ) )
      } ) )
    go( this )
  }

  override protected def stepString( subProofLabels: Map[Any, String] ) =
    s"${clause.mkString( " " )}    (${super.stepString( subProofLabels )})"
}
object Res {
  case class Taut( v: Int ) extends Res {
    require( v > 0 )
    val clause = Set( v, -v )
    def immediateSubProofs: Seq[Res] = Seq()
  }
  case class Input( clause: Clause ) extends Res {
    def immediateSubProofs: Seq[Res] = Seq()
  }
  case class Resolve( a: Res, b: Res, v: Int ) extends Res {
    require( v > 0 )
    val clause = ( a.clause - v ) union ( b.clause - ( -v ) )
    def immediateSubProofs: Seq[Res] = Seq( a, b )
  }
  object Resolve {
    def f( a: Res, b: Res, v: Int ): Res =
      ( a, b ) match {
        case ( Taut( _ ), _ )            => b
        case ( _, Taut( _ ) )            => a
        case _ if b.clause.contains( v ) => Resolve( b, a, v )
        case _                           => Resolve( a, b, v )
      }
  }
}
