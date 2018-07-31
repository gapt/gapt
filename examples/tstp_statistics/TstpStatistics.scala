package gapt.examples.tstp_statistics

import ammonite.ops.FilePath
import gapt.examples.tstp_statistics.Types.{ ClauseId, RuleName }
import gapt.formats.tptp.{ TptpFile, TptpParser, TptpProofParser }
import gapt.proofs.HOLSequent
import gapt.proofs.resolution.ResolutionProof
import gapt.proofs.sketch.RefutationSketchToResolution
import gapt.utils.{ TimeOutException, withTimeout }

import scala.collection.mutable
import scala.concurrent.duration._

object Types {
  type RuleName = String
  type ClauseId = String
}

case class Statistic(
    min:    Int,
    max:    Int,
    avg:    Int,
    median: Int )

/*
   Invariants:
   dagSize <= treeSize
   dept <= size
 */
case class RPProofStats(
    name:             String,
    dagSize:          BigInt,
    treeSize:         BigInt,
    depth:            Int,
    rule_histogram:   Map[RuleName, Int],
    clause_frequency: Map[ClauseId, ( RuleName, Int )],
    subst_term_sizes: Statistic,
    reused_axioms:    Map[RuleName, ( HOLSequent, Int )],
    reused_derived:   Map[RuleName, ( HOLSequent, Int )] )

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

    val stats = RPProofStats( name, dagSize, treeSize, depth, hist.toMap, freq.toMap,
      Statistic( 0, 0, 0, 0 ), fst_map( reused_axioms ), fst_map( reused_derived ) )
    stats

  }

}
