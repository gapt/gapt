package gapt.formats.tptp.statistics

import ammonite.ops.{ Path, exists }
import gapt.expr._
import gapt.formats.csv.{ CSVFile, CSVRow }
import gapt.formats.tptp._
import gapt.proofs.resolution._
import gapt.proofs.sketch.RefutationSketchToResolution
import gapt.utils.{ Statistic, TimeOutException, withTimeout }

import scala.collection.mutable
import scala.compat.Platform.StackOverflowError
import scala.concurrent.duration._

@SerialVersionUID( 700000L )
sealed abstract class TstpError[T <: FileData]( val file: T ) extends Serializable
@SerialVersionUID( 700001L )
case class FileNotFound[T <: FileData]( override val file: T ) extends TstpError( file )
@SerialVersionUID( 700002L )
case class MalformedFile[T <: FileData]( override val file: T ) extends TstpError( file )
@SerialVersionUID( 700003L )
case class ParsingError[T <: FileData]( override val file: T ) extends TstpError( file )
@SerialVersionUID( 700004L )
case class ReconstructionGaveUp[T <: FileData]( override val file: T ) extends TstpError( file )
@SerialVersionUID( 700005L )
case class ReconstructionTimeout[T <: FileData]( override val file: T ) extends TstpError( file )
@SerialVersionUID( 700006L )
case class ReconstructionError[T <: FileData]( override val file: T ) extends TstpError( file )
@SerialVersionUID( 700008L )
case class StackOverflow[T <: FileData]( override val file: T ) extends TstpError( file )

@SerialVersionUID( 700010L )
case class ErrorBags[T <: FileData](
    nf: Iterable[FileNotFound[T]],
    mf: Iterable[MalformedFile[T]],
    pe: Iterable[ParsingError[T]],
    rg: Iterable[ReconstructionGaveUp[T]],
    rt: Iterable[ReconstructionTimeout[T]],
    re: Iterable[ReconstructionError[T]],
    so: Iterable[StackOverflow[T]] ) extends Serializable {
  def printSizes = {
    println( s"file not found : ${nf.size}" )
    println( s"malformed file : ${mf.size}" )
    println( s"parsiong error : ${pe.size}" )
    println( s"gave up        : ${rg.size}" )
    println( s"timeout        : ${rt.size}" )
    println( s"replay error   : ${re.size}" )
    println( s"stack overflow : ${so.size}" )
  }

}

object ErrorBags {
  def toCSV[T <: FileData]( x: ErrorBags[T] ) = x match {
    case ErrorBags( a, b, c, d, e, f, g ) =>
      CSVRow( List( a.size, b.size, c.size, d.size, e.size, f.size, g.size ) )
  }

  def filter[T <: FileData]( bag: ErrorBags[T], prop: T => Boolean ) = bag match {
    case ErrorBags( a, b, c, d, e, f, g ) =>
      ErrorBags(
        a.filter( x => prop( x.file ) ),
        b.filter( x => prop( x.file ) ),
        c.filter( x => prop( x.file ) ),
        d.filter( x => prop( x.file ) ),
        e.filter( x => prop( x.file ) ),
        f.filter( x => prop( x.file ) ),
        g.filter( x => prop( x.file ) ) )
  }
}

object TstpStatistics {

  def apply[T <: FileData]( file: T, print_statistics: Boolean = false ): ( Option[TptpFile], Either[TstpError[T], RPProofStats[T]] ) = {
    loadFile( file, print_statistics ) match {
      case ( tstpo, rpo ) =>
        ( tstpo, rpo.map( getRPStats( file, _ ) ) )

    }
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

  def loadFile[T <: FileData]( v: T, print_statistics: Boolean = false ): ( Option[TptpFile], Either[TstpError[T], ResolutionProof] ) = {
    if ( exists( Path( v.fileName ) ) ) {
      val tstpf_file: Option[TptpFile] = try {
        Some( TptpParser.load( v.file ) )

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
          ( None, Left( ParsingError( v ) ) )
        case _ =>
          try {
            withTimeout( 120.seconds ) {
              val ( formula, sketch ) = TptpProofParser.parse( v.file, true )
              RefutationSketchToResolution( sketch ) match {
                case Left( unprovable ) =>
                  if ( print_statistics ) {
                    println( s"can't reconstruct $v" )
                  }
                  ( tstpf_file, Left( ReconstructionGaveUp( v ) ) )
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
              ( tstpf_file, Left( ReconstructionTimeout( v ) ) )
            case e: MalformedInputFileException =>
              if ( print_statistics ) {
                println()
                println( s"malformed input file $v" )
              }
              ( tstpf_file, Left( MalformedFile( v ) ) )
            case e: Exception =>
              if ( print_statistics ) {
                println()
                println( s"reconstruction error $v" )
                e.printStackTrace()
              }
              ( tstpf_file, Left( ReconstructionError( v ) ) )
            case e: StackOverflowError =>
              if ( print_statistics ) {
                println()
                println( s"reconstruction error $v (stack overflow)" )
              }
              ( tstpf_file, Left( StackOverflow( v ) ) )
          }
      }
    } else ( None, Left( FileNotFound( v ) ) )
  }

  def resultToCSV[T <: FileData]( rpstats: Iterable[RPProofStats[T]] ) = {
    CSVFile( RPProofStats.csv_header, rpstats.toSeq.map( _.toCSV ), CSVFile.defaultSep )
  }

  //some tools for pre- and postprocessing
  def filterExisting[T <: FileData]( coll: Iterable[T] ) =
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

  def bagErrors[T <: FileData]( errors: Iterable[TstpError[T]] ) = {
    val nf = mutable.Set[FileNotFound[T]]()
    val mf = mutable.Set[MalformedFile[T]]()
    val pe = mutable.Set[ParsingError[T]]()
    val rg = mutable.Set[ReconstructionGaveUp[T]]()
    val rt = mutable.Set[ReconstructionTimeout[T]]()
    val re = mutable.Set[ReconstructionError[T]]()
    val so = mutable.Set[StackOverflow[T]]()

    errors foreach {
      case e @ FileNotFound( file )          => nf.add( e )
      case e @ MalformedFile( file )         => mf.add( e )
      case e @ ParsingError( file )          => pe.add( e )
      case e @ ReconstructionGaveUp( file )  => rg.add( e )
      case e @ ReconstructionTimeout( file ) => rt.add( e )
      case e @ ReconstructionError( file )   => re.add( e )
      case e @ StackOverflow( file )         => so.add( e )
    }

    ErrorBags( nf, mf, pe, rg, rt, re, so )
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

