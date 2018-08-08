package gapt.formats.tptp.statistics

import ammonite.ops.{ FilePath, Path, exists }
import gapt.expr._
import gapt.formats.tptp.{ TptpFile, TptpParser, TptpProofParser }
import gapt.proofs.resolution._
import gapt.proofs.sketch.RefutationSketchToResolution
import gapt.utils.{ Statistic, TimeOutException, withTimeout }

import scala.collection.mutable
import scala.compat.Platform.StackOverflowError
import scala.concurrent.duration._

object TstpStatistics {

  def apply[T <: FileData]( file: T, print_statistics: Boolean = false ): ( Option[TptpFile], Either[( String, String ), RPProofStats[T]] ) = {
    loadFile( file, print_statistics ) match {
      case ( tstpo, rpo ) =>
        ( tstpo, rpo.map( getRPStats( file, _ ) ) )

    }
  }

  def filterExisting[T <: FileData, Q <: Iterable[T]]( coll: Q ) =
    coll.filter( x => exists( Path( x.fileName ) ) )

  def bagResults[T <: CASCResult]( m: Map[T, RPProofStats[T]] ) = {
    val all_solvers = m.keySet.map( _.prover )
    val solver_count = all_solvers.size

    val byProver = mutable.Map[Prover, Set[RPProofStats[T]]]()
    m.foreach { case ( k, v ) => byProver( k.prover ) = byProver.getOrElse( k.prover, Set() ) + v }

    val byProblem = mutable.Map[Problem, Set[RPProofStats[T]]]()
    m.foreach { case ( k, v ) => byProver( k.problem ) = byProver.getOrElse( k.problem, Set() ) + v }

    val allSolved = byProblem.filter( _._2.size == solver_count )

    ( byProver.toMap, byProblem.toMap, allSolved.toMap )
  }

  def applyAll[T <: FileData]( pfiles: Iterable[T], print_statistics: Boolean = false ) = {
    val max = pfiles.size
    var count = 0

    val ( tstps, rps ) = pfiles.par.map( i => {
      val r @ ( m1, m2 ) = apply( i, print_statistics )
      if ( print_statistics ) {
        ( m1.isEmpty, m2.isLeft ) match {
          case ( true, _ )      => print( "o" )
          case ( false, true )  => print( "x" )
          case ( false, false ) => print( "." )
        }
        count = count + 1 //not thread safe but it's just for the output
        val percent = ( 100 * count ) / max
        if ( percent % 5 == 0 ) {
          println( s"\n$percent %" )
        }

      }
      r
    } ).unzip

    val rpmap = mutable.Map() ++ ( rps.flatMap {
      case Right( stat ) => ( stat.name, stat ) :: Nil
      case Left( _ )     => Nil
    } )

    val rperrormap = rps.flatMap {
      case Right( _ )  => Nil
      case Left( msg ) => msg :: Nil
    }.toList

    ( tstps.flatMap( ( x: Option[TptpFile] ) => x ), rpmap, rperrormap )

  }

  def loadFile( v: FileData, print_statistics: Boolean = false ): ( Option[TptpFile], Either[( String, String ), ResolutionProof] ) = {
    val tstpf_file: Option[TptpFile] = try {
      Some( TptpParser.load( FilePath( v.fileName ) ) )

    } catch {
      case e: Exception =>
        if ( print_statistics ) {
          println( s"parser error $v" )
        }
        None
    }

    tstpf_file match {
      case None =>
        //don't try to reconstruct the proof if we can't read it
        ( None, Left( ( s"parser error", v.fileName ) ) )
      case _ =>
        try {
          withTimeout( 120.seconds ) {
            val ( formula, sketch ) = TptpProofParser.parse( FilePath( v.fileName ), true )
            RefutationSketchToResolution( sketch ) match {
              case Left( unprovable ) =>
                if ( print_statistics ) {
                  println( s"can't reconstruct $v" )
                }
                ( tstpf_file, Left( ( s"can't reconstruct", v.fileName ) ) )
              case Right( proof ) =>
                ( tstpf_file, Right( proof ) )
            }
          }
        } catch {
          case e: TimeOutException =>
            if ( print_statistics ) {
              println()
              println( s"reconstruction timeout $v" )
            }
            ( tstpf_file, Left( ( s"reconstruction timeout", v.fileName ) ) )
          case e: Exception =>
            if ( print_statistics ) {
              println()
              println( s"reconstruction error $v" )
            }
            if ( print_statistics ) {
              print( s"bug reconstructing $v.filename" )
              e.printStackTrace()
            }
            ( tstpf_file, Left( ( s"reconstruction bug ${e.getMessage}", v.fileName ) ) )
          case e: StackOverflowError =>
            if ( print_statistics ) {
              println()
              println( s"reconstruction error $v (stack overflow)" )
            }
            ( tstpf_file, Left( ( s"reconstruction error $v (stack overflow)", v.fileName ) ) )
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

  def getRPStats[T <: FileData]( name: T, rp: ResolutionProof ): RPProofStats[T] = {
    val dagSize = rp.dagLike.size
    val treeSize = rp.treeLike.size
    val depth = rp.depth
    val hist = mutable.Map[RuleName, Int]()

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

    val clause_sizes_dag = Statistic( rp.dagLike.postOrder.flatMap( x => x.conclusion.size :: Nil ) )

    val freq = mutable.Map[ClauseId, ( RuleName, Int )]() //TODO: fill in

    val stats = RPProofStats( name, dagSize, treeSize, depth, hist.toMap, freq.toMap,
      getSubstStats( subst_sizes ), getSubstStats( subst_depths ),
      fst_map( reused_axioms ), fst_map( reused_derived ), clause_sizes_dag )

    stats
  }
}

