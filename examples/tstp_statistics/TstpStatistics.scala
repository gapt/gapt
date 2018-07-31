package gapt.examples.tstp_statistics

import ammonite.ops.FilePath
import gapt.examples.tstp_statistics.Types.{ ClauseId, RuleName }
import gapt.expr.{ Abs, App, Const, Expr, Substitution, Var }
import gapt.formats.tptp.{ TptpFile, TptpParser, TptpProofParser }
import gapt.proofs.HOLSequent
import gapt.proofs.resolution.{ ResolutionProof, Subst }
import gapt.proofs.sketch.RefutationSketchToResolution
import gapt.utils.{ TimeOutException, withTimeout }

import scala.collection.mutable
import scala.concurrent.duration._

object Types {
  type RuleName = String
  type ClauseId = String
}

case class Statistic(
    n:      BigInt,
    min:    BigInt,
    max:    BigInt,
    avg:    BigDecimal,
    median: BigDecimal )

object Statistic {
  def apply( values: Seq[Int] ): Statistic = {
    require( values.nonEmpty, "Need data to compute statistics" )

    val sorted = values.sorted
    val initial = sorted.head

    val _n = values.size
    var _min: BigInt = initial
    var _max: BigInt = initial
    var _sum: BigInt = initial

    for ( data <- sorted.tail ) {
      _min = _min.min( data )
      _max = _max.max( data )
      _sum = _sum + data
    }
    val _avg: BigDecimal = BigDecimal( _sum ) / BigDecimal( _n )
    val _median: BigDecimal = _n % 2 match {
      case 0 =>
        val m1 = BigDecimal( sorted( _n / 2 ) )
        val m2 = BigDecimal( sorted( ( _n / 2 ) - 1 ) )
        ( m1 + m2 ) / 2
      case 1 =>
        BigDecimal( sorted( _n / 2 ) )
      case _ =>
        throw new IllegalArgumentException( "Result of % 2 should always be 0 or 1!" )
    }

    Statistic( _n, _min, _max, _avg, _median )
  }

}

/*
   Invariants:
   dagSize <= treeSize
   dept <= size
 */
case class RPProofStats(
    name:              String,
    dagSize:           BigInt,
    treeSize:          BigInt,
    depth:             Int,
    rule_histogram:    Map[RuleName, Int],
    clause_frequency:  Map[ClauseId, ( RuleName, Int )],
    subst_term_sizes:  Option[Statistic],
    subst_term_depths: Option[Statistic],
    reused_axioms:     Map[RuleName, ( HOLSequent, Int )],
    reused_derived:    Map[RuleName, ( HOLSequent, Int )] )

/*
   Invariants:
   dagSize <= treeSize
   dept <= size
 */
case class TstpProofStats(
    name:             String,
    dagSize:          BigInt,
    treeSize:         BigInt,
    depth:            Int,
    rule_histogram:   mutable.Map[RuleName, Int],
    clause_frequency: mutable.Map[ClauseId, ( RuleName, Int )] )

/*
   Invariants:
    axiom_count <= input_formula_count
    constants + unary_funs + binary_funs <= signature_size
 */
case class InputStats(
    name:                String,
    axiom_count:         Int,
    input_formula_count: Int,
    signature_size:      Int,
    constants:           Int,
    unary_funs:          Int,
    binary_funs:         Int,
    max_arity:           Int,
    median_arity:        Int )

object TstpStatistics {
  def applyAll( pfiles: Iterable[String] ) = {

    for ( i <- pfiles ) {
      val ( m1, m2 ) = TstpStatistics( i );
      ( m1.isEmpty, m2.isEmpty ) match {
        case ( true, _ )      => print( "o" )
        case ( false, true )  => print( "x" )
        case ( false, false ) => print( "." )
      }
    }
  }

  def apply( file: String ) = {
    loadFile( file ) match {
      case ( tstpo, rpo ) =>
        ( tstpo, rpo.map( getRPStats( file, _ ) ) )

    }
  }

  def loadFile( v: String ): ( Option[TptpFile], Option[ResolutionProof] ) = {
    val tstpf_file: Option[TptpFile] = try {
      Some( TptpParser.load( FilePath( v ) ) )

    } catch {
      case e: Exception =>
        println( s"can't load $v" );
        None
    }

    tstpf_file match {
      case None =>
        //don't try to reconstruct the proof if we can't read it
        ( None, None )
      case _ =>
        try {
          withTimeout( 120.seconds ) {
            val ( formula, sketch ) = TptpProofParser.parse( FilePath( v ), true )
            RefutationSketchToResolution( sketch ) match {
              case Left( unprovable ) =>
                println( s"can't reconstruct $v" )
                ( tstpf_file, None )
              case Right( proof ) =>
                ( tstpf_file, Some( proof ) )
            }
          }
        } catch {
          case e: TimeOutException =>
            println( s"reconstruction timeout $v" )
            ( tstpf_file, None )
          case _: Exception =>
            println( s"reconstruction error $v" )
            ( tstpf_file, None )
        }
    }
  }

  private def inc_rule_count[T]( r: T, rule_histogram: mutable.Map[T, Int] ) = {
    rule_histogram( r ) = rule_histogram.getOrElse( r, 0 ) + 1
  }

  private def fst_map[U, V, W, X]( m: mutable.Map[U, ( V, W, X )] ) =
    m.map( x => ( x._1, ( x._2._1, x._2._2 ) ) ).toMap

  private def term_depth_size( t: Expr ): ( Int, Int ) = t match {
    case Var( _, _ ) | Const( _, _, _ ) => ( 1, 1 )
    case Abs( _, s ) =>
      val d = term_depth_size( s )
      ( d._1 + 1, d._2 + 1 )
    case App( a, b ) =>
      val ( d1a, d1b ) = term_depth_size( a )
      val ( d2a, d2b ) = term_depth_size( b )
      ( d1a.max( d2a ) + 1, d1b + d2b + 1 )
  }

  private def getSubstDepths( s: Substitution ) =
    s.map.values.map( term_depth_size( _ ) )

  private def getSubstStats( l: Seq[Int] ) = {
    val filtered = l.filter( _ > 0 )
    if ( filtered.nonEmpty ) Some( Statistic( filtered ) ) else None
  }

  def getRPStats( name: String, rp: ResolutionProof ) = {
    val dagSize = rp.dagLike.size
    val treeSize = rp.treeLike.size
    val depth = rp.depth
    val hist = mutable.Map[RuleName, Int]()
    val freq = mutable.Map[ClauseId, ( RuleName, Int )]()

    val subproof_count = rp.subProofs.size
    val ids = ( 1 to subproof_count ).map( "node" + _ )

    val names = mutable.Map[RuleName, ResolutionProof]() ++ ( ids zip rp.subProofs )
    val rnames = mutable.Map[ResolutionProof, RuleName]() ++ ( rp.subProofs zip ids )

    require( rnames.size == subproof_count )

    for ( ( r, id ) <- rnames ) {
      r.immediateSubProofs.map( x => inc_rule_count( rnames( x ), hist ) )
    }

    val reused_proofs = hist.flatMap {
      case ( n, freq ) if freq > 1 =>
        val p = names( n )
        ( n, ( p.conclusion, freq, p.immediateSubProofs.isEmpty ) ) :: Nil
      case _ => Nil
    }

    val ( reused_axioms, reused_derived ) = reused_proofs.partition( _._2._3 )

    val ( subst_depths, subst_sizes ) = rp.subProofs.toSeq.flatMap {
      case Subst( _, subst ) =>
        getSubstDepths( subst )
      case _ => Seq()
    }.unzip

    val stats = RPProofStats( name, dagSize, treeSize, depth, hist.toMap, freq.toMap,
      getSubstStats( subst_sizes ), getSubstStats( subst_depths ),
      fst_map( reused_axioms ), fst_map( reused_derived ) )

    stats
  }

}
