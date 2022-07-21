package gapt.formats.tptp.statistics

import ammonite.ops.{ Path, exists }
import gapt.expr._
import gapt.expr.formula.Formula
import gapt.expr.subst.Substitution
import gapt.expr.util.expressionDepth
import gapt.expr.util.expressionSize
import gapt.formats.csv.{ CSVFile, CSVRow }
import gapt.formats.tptp._
import gapt.proofs.{ HOLSequent, Sequent }
import gapt.proofs.resolution._
import gapt.proofs.sketch.{ RefutationSketch, RefutationSketchToResolution }
import gapt.utils.{ Statistic, TimeOutException, withTimeout }

import java.lang.StackOverflowError

import scala.collection.mutable
import scala.concurrent.duration._
import scala.collection.parallel.CollectionConverters._

//TODO: make a common superclass for TstpProofStats and RPProofStats

/**
 * Describes various errors that may occur during proof replay
 * @param file The file with the TSTP proof that was replayed
 * @tparam T an instance of [[FileData]]
 */
@SerialVersionUID( 700000L )
sealed abstract class TstpError[+T <: FileData]( val file: T ) extends Serializable

/**
 * Companion object to [[TstpError]].
 */
object TstpError {
  /**
   * Converts an error to a CSV row: fileName, error type
   * @param e the error to be converted
   * @tparam T an instance of [[FileData]]
   * @return a CSV row describing the error type
   */
  def toCSV[T <: FileData]( e: TstpError[T] ): CSVRow[String] = {

    val tp: String = e match {
      case FileNotFound( _ )          => "FileNotFound"
      case MalformedFile( _ )         => "MalformedFile"
      case ParsingError( _ )          => "ParsingError"
      case ReconstructionError( _ )   => "ReconstructionError"
      case ReconstructionGaveUp( _ )  => "ReconstructionGaveUp"
      case ReconstructionTimeout( _ ) => "ReconstuctionTimeout"
      case StackOverflow( _ )         => "StackOverflow"
    }

    val row = e.file match {
      case r @ CASCResult( path, prover, problem, extension ) =>
        Seq( prover, problem )
      case r: FileData =>
        Seq( r.fileName )
    }

    CSVRow( row :+ tp )
  }
}

/**
 * Signifies that the file file.fileName does not exists
 * @param file The file with the TSTP proof that was replayed
 * @tparam T an instance of [[FileData]]
 */
@SerialVersionUID( 700001L )
case class FileNotFound[+T <: FileData]( override val file: T ) extends TstpError( file )

/**
 * Signifies an error in the TSTP DAG
 * @param file The file with the TSTP proof that was replayed
 * @tparam T an instance of [[FileData]]
 */
@SerialVersionUID( 700002L )
case class MalformedFile[+T <: FileData]( override val file: T ) extends TstpError( file )

/**
 * Signifies other exception that were thrown during sketch construction (e.g. the file is syntactically incorrect)
 * @param file The file with the TSTP proof that was replayed
 * @tparam T an instance of [[FileData]]
 */
@SerialVersionUID( 700003L )
case class ParsingError[+T <: FileData]( override val file: T ) extends TstpError( file )

/**
 * Signifies a termination of `RefutationSketchToResolution.apply()` that could not replay a step.
 * @param file The file with the TSTP proof that was replayed
 * @tparam T an instance of [[FileData]]
 */
@SerialVersionUID( 700004L )
case class ReconstructionGaveUp[+T <: FileData]( override val file: T ) extends TstpError( file )

/**
 * Signifies a timeout from [[gapt.utils.withTimeout]] during reconstruction.
 * @param file The file with the TSTP proof that was replayed
 * @tparam T an instance of [[FileData]]
 */
@SerialVersionUID( 700005L )
case class ReconstructionTimeout[+T <: FileData]( override val file: T ) extends TstpError( file )

/**
 * Siginifies an exception during proof replay, e.g. attempting to apply a split where variables in the split clauses are not disjoint
 * @param file The file with the TSTP proof that was replayed
 * @tparam T an instance of [[FileData]]
 */
@SerialVersionUID( 700006L )
case class ReconstructionError[+T <: FileData]( override val file: T ) extends TstpError( file )

/**
 * Signifies a stack overflow
 * @param file The file with the TSTP proof that was replayed
 * @tparam T an instance of [[FileData]]
 */
@SerialVersionUID( 700008L )
case class StackOverflow[+T <: FileData]( override val file: T ) extends TstpError( file )

/**
 * Divides a list of [[TstpError]] into its sublasses
 * @param nf file not found
 * @param mf malformed file
 * @param pe parsing error
 * @param rg reconstruction gave up
 * @param rt reconstruction timeout
 * @param re reconstruction error
 * @param so stack overflow
 * @tparam T an instance of [[FileData]] to describe files
 */
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

  def resourceErrors() = rt ++ so
  def internalErrors() = pe ++ re ++ rg

}

/**
 * Companion object to [[ErrorBags]]
 */
object ErrorBags {
  /**
   * Convert error bag sizes to CSV
   * @param x an error bag
   * @tparam T the [[FileData]] describing
   * @return
   */
  def toCSV[T <: FileData]( x: ErrorBags[T] ) = x match {
    case ErrorBags( a, b, c, d, e, f, g ) =>
      CSVRow( List( a.size, b.size, c.size, d.size, e.size, f.size, g.size ) )
  }

  /**
   * Filter error bags by a property
   * @param bag the bag to filter
   * @param prop the property
   * @tparam T an instance of [[FileData]]
   * @return the filtered bag
   */
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

/**
 * Calculates sketch statistics ([[TstpProofStats]]) and replay statistics ([[RPProofStats]]) from
 * a list of [[FileData]] files as well as errors. Provides serialization to a file.
 */
object TstpStatistics {

  /**
   * Calculate sketch statistics ([[TstpProofStats]]) and replay statistics ([[RPProofStats]]) for a given
   * file. If the sketch has a failure, the replay has one as well/
   * @param file the file to parse
   * @param print_statistics print parsing statistics to stdout
   * @tparam T an instance of [[FileData]] describing the input file
   * @return either:
   *         * a tuple of errors
   *         * a tuple of a proof sketch statistic and a replay error
   *         * a tuple of a proof sketch statistic and a replay statistic
   */
  def apply[T <: FileData]( file: T, print_statistics: Boolean = false ): ( Either[TstpError[T], TstpProofStats[T]], Either[TstpError[T], RPProofStats[T]] ) = {
    loadFile( file, print_statistics ) match {
      case ( tstpo, rpo ) =>
        ( tstpo.map( getTSTPStats( file, _ ) ), rpo.map( getRPStats( file, _ ) ) )
    }
  }

  /**
   * Apply [[TstpStatistics.apply]] to a list of files
   * @param pfiles the files to parse
   * @param print_statistics print parsing statitics and progress to stdout (helpful for large batches of files)
   * @tparam T an instance of [[FileData]] describing the input file
   * @return a [[ResultBundle]] mapping files to the corresponding statistics or errors
   */
  def applyAll[T <: FileData]( pfiles: Iterable[T], print_statistics: Boolean = false ) = {
    val max = pfiles.size
    var count = 0

    val ( tstps, rps ) = pfiles.par.map( i => {
      val r @ ( m1, m2 ) = apply( i, print_statistics )
      if ( print_statistics ) {
        ( m1.isLeft, m2.isLeft ) match {
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

    val tstpmap = mutable.Map() ++ ( tstps.flatMap {
      case Right( stat ) => ( stat.name, stat ) :: Nil
      case Left( _ )     => Nil
    } )

    val tstpperrormap = tstps.flatMap {
      case Right( _ )  => Nil
      case Left( msg ) => msg :: Nil
    }.toList

    ResultBundle( tstpmap.toMap, rpmap.toMap, tstpperrormap, rperrormap )

  }

  /**
   * Load a proof sketch and a replayed proof from a file, if possible
   * @param v the file to parse
   * @param print_statistics print statistics to stdout
   * @tparam T the [[FileData]] instance used to describe files
   * @return a tuple of either
   *         * two [[TstpError]]s
   *         * a refutation sketch and a [[TstpError]]
   *         * a refutation sketch and a resolution proof.
   */
  def loadFile[T <: FileData]( v: T, print_statistics: Boolean = false ): ( Either[TstpError[T], RefutationSketch], Either[TstpError[T], ResolutionProof] ) = {
    if ( exists( Path( v.fileName ) ) ) {
      val tstp_sketch = loadSketch( v, print_statistics )
      val replayed = replaySketch( v, tstp_sketch, print_statistics )
      ( tstp_sketch, replayed )
    } else ( Left( FileNotFound( v ) ), Left( FileNotFound( v ) ) )
  }

  /**
   * Loads a sketch from a [[FileData]] file
   * @param v the file to load
   * @param print_statistics print details about errors that occur
   * @tparam T an instance of [[FileData]] to describe the input file
   * @return either a [[TstpError]] describing what failed or a refutation sketch.
   */
  def loadSketch[T <: FileData]( v: T, print_statistics: Boolean = false ): Either[TstpError[T], RefutationSketch] = try {
    withTimeout( 120.seconds ) {
      Right( TptpProofParser.parse( v.file, true )._2 )
    }
  } catch {
    case e: TimeOutException =>
      if ( print_statistics ) {
        println( s"parser timeout $v" )
      }
      Left( ReconstructionTimeout( v ) )
    case e: MalformedInputFileException =>
      if ( print_statistics ) {
        println( s"malformed file: $v" )
      }
      Left( MalformedFile( v ) )
    case e: Exception =>
      if ( print_statistics ) {
        println( s"parser error $v" )
      }
      Left( ParsingError( v ) )
    case e: java.lang.StackOverflowError =>
      if ( print_statistics ) {
        println( s"parser timeout $v" )
      }
      Left( StackOverflow( v ) )
  }

  /**
   * Replays a sketch
   * @param v the source file of the sketch
   * @param tstp_sketch the sketch to replay
   * @param print_statistics print details about errors that occur
   * @tparam T an instance of [[FileData]] to describe the input file
   * @return either a [[TstpError]] describing what failed or a resolution proof.
   */
  def replaySketch[T <: FileData]( v: T, tstp_sketch: Either[TstpError[T], RefutationSketch], print_statistics: Boolean = false ): Either[TstpError[T], ResolutionProof] = tstp_sketch match {
    case Left( _ ) =>
      //don't try to reconstruct the proof if we can't read it
      Left( ParsingError( v ) )
    case Right( sketch ) =>
      try {
        withTimeout( 120.seconds ) {
          RefutationSketchToResolution( sketch ) match {
            case Left( unprovable ) =>
              if ( print_statistics ) {
                println( s"can't reconstruct $v" )
              }
              Left( ReconstructionGaveUp( v ) )
            case Right( proof ) =>
              Right( proof )
          }
        }
      } catch {
        case e: TimeOutException =>
          if ( print_statistics ) {
            println()
            println( s"reconstruction timeout $v" )
          }
          Left( ReconstructionTimeout( v ) )
        case e: MalformedInputFileException =>
          if ( print_statistics ) {
            println()
            println( s"malformed input file $v" )
          }
          Left( MalformedFile( v ) )
        case e: Exception =>
          if ( print_statistics ) {
            println()
            println( s"reconstruction error $v" )
            e.printStackTrace()
          }
          Left( ReconstructionError( v ) )
        case e: StackOverflowError =>
          if ( print_statistics ) {
            println()
            println( s"reconstruction error $v (stack overflow)" )
          }
          Left( StackOverflow( v ) )
      }
  }

  /**
   * Converts a list of [[RPProofStats]] to a CSV File
   * @param rpstats the stats to convert
   * @tparam T the [[FileData]] instance describing a TSTP file
   * @return a CSV file with a row for each element in rpstats
   */
  def resultToCSV[T <: FileData]( rpstats: Iterable[RPProofStats[T]] ) = {
    //TODO: move to RPProofStats
    CSVFile( RPProofStats.csv_header, rpstats.toSeq.map( _.toCSV() ), CSVFile.defaultSep )
  }

  //some tools for pre- and postprocessing

  /**
   * Remove non-existsing files from a list of [[FileData]]s
   * @param coll a list of files
   * @tparam T the instance of [[FileData]] describing a file
   * @return the filtered list
   */
  def filterExisting[T <: FileData]( coll: Iterable[T] ) =
    coll.filter( x => exists( Path( x.fileName ) ) )

  /**
   * Divide a maping of CASCResults into submaps for each prover, each problem and those that were solved by all provers
   * @param m a map from [[CASCResult]]s to arbitrary data (intended for [[TstpProofStats]] / [[RPProofStats]] )
   * @tparam S an instance of [[CASCResult]] (which is an instance of [[FileData]])
   * @tparam T the value type of the m
   * @return a triple of maps, grouping the vakyes of m ...
   *         1) by prover
   *         2) by problem
   *         3) the subset of 1) that has been solved by all provers
   */
  def bagResults[S <: CASCResult, T]( m: Map[S, T] ) = {
    val all_solvers = m.keySet.map( _.prover )
    val solver_count = all_solvers.size

    val byProver = mutable.Map[Prover, Set[T]]()
    m.foreach { case ( k, v ) => byProver( k.prover ) = byProver.getOrElse( k.prover, Set() ) + v }

    val byProblem = mutable.Map[Problem, Set[T]]()
    m.foreach { case ( k, v ) => byProblem( k.problem ) = byProblem.getOrElse( k.problem, Set() ) + v }

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
    val so: mutable.Set[StackOverflow[T]] = mutable.Set()

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

  //can't serialize sequents so we convert them to strings
  private def fst_map_c[U, V, W, X]( m: mutable.Map[U, ( V, W, X )] ) =
    m.map( x => ( x._1, ( x._2._1.toString, x._2._2 ) ) ).toMap

  private def getSubstDepths( s: Substitution ) =
    s.map.values.map( x => ( expressionDepth( x ), expressionSize( x ) ) )

  private def getSubstStats( l: Seq[Int] ) = {
    val filtered = l.filter( _ > 0 )
    if ( filtered.nonEmpty ) Some( Statistic( filtered ) ) else None
  }

  def clauseWeight( s: HOLSequent ): Int = {
    ( s.antecedent ++ s.antecedent ).foldLeft( 0 )( ( weight, formula ) => weight + expressionSize( formula ) )
  }

  /**
   * Calculates [[RPProofStats]] for a given resolution proof.
   * @param name the file containing rp
   * @param rp the replayed proof
   * @tparam T the instance of [[FileData]] describing the file name
   * @return proof statistic for rp
   */
  def getRPStats[T <: FileData]( name: T, rp: ResolutionProof ): RPProofStats[T] = {
    val dagSize = rp.dagLike.size
    val treeSize = rp.treeLike.size
    val depth = rp.depth
    val hist = mutable.Map[RuleName, Int]()
    val freq = mutable.Map[ClauseId, Int]()

    val subproof_count = rp.subProofs.size
    val ids = ( 1 to subproof_count ).map( "node" + _ )

    val names = mutable.Map[ClauseId, ResolutionProof]() ++ ( ids zip rp.subProofs )
    val rnames = mutable.Map[ResolutionProof, ClauseId]() ++ ( rp.subProofs zip ids )

    require( rnames.size == subproof_count )

    for ( ( r, id ) <- rnames ) {
      r.immediateSubProofs.map( x => {
        inc_rule_count( x.name, hist ) //count rule name
        inc_rule_count( rnames( x ), freq ) //count clause id
      } )
    }

    val reused_proofs = freq.flatMap {
      case ( n, freq: Int ) if freq > 1 =>
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

    val ( csizes, cweights ) = rp.dagLike.postOrder.flatMap( x => ( x.conclusion.size, clauseWeight( x.conclusion ) ) :: Nil ).unzip
    val clause_sizes = Statistic( csizes )
    val clause_weights = Statistic( cweights )

    val stats = RPProofStats( name, dagSize, treeSize, depth, hist.toMap, freq.toMap,
      fst_map_c( reused_axioms ), fst_map_c( reused_derived ), clause_sizes, clause_weights,
      getSubstStats( subst_sizes ), getSubstStats( subst_depths ) )

    stats
  }

  /**
   * Calculates [[TstpProofStats]] for a given refutation sketch.
   * @param name the file containing the sketch
   * @param rp the proof sketch
   * @tparam T the instance of [[FileData]] describing the file name
   * @return proof statistic for rp
   */
  def getTSTPStats[T <: FileData]( name: T, rp: RefutationSketch ): TstpProofStats[T] = {
    val dagSize = rp.dagLike.size
    val treeSize = rp.treeLike.size
    val depth = rp.depth
    val hist = mutable.Map[RuleName, Int]()
    val freq = mutable.Map[ClauseId, Int]()

    val subproof_count = rp.subProofs.size
    val ids = ( 1 to subproof_count ).map( "node" + _ )

    val names = mutable.Map[ClauseId, RefutationSketch]() ++ ( ids zip rp.subProofs )
    val rnames = mutable.Map[RefutationSketch, ClauseId]() ++ ( rp.subProofs zip ids )

    require( rnames.size == subproof_count )

    for ( ( r, id ) <- rnames ) {
      r.immediateSubProofs.map( x => {
        inc_rule_count( x.name, hist ) //count rule names
        inc_rule_count( rnames( x ), freq ) //count clause occurrences
      } )
    }

    val reused_proofs = freq.flatMap {
      case ( n, freq ) if freq > 1 =>
        val p = names( n )
        ( n, ( p.conclusion, freq, p.immediateSubProofs.isEmpty ) ) :: Nil
      case _ => Nil
    }

    val ( reused_axioms, reused_derived ) = reused_proofs.partition( _._2._3 )

    val ( csizes, cweights ) = rp.dagLike.postOrder.flatMap( x => ( x.conclusion.size, clauseWeight( x.conclusion ) ) :: Nil ).unzip
    val clause_sizes = Statistic( csizes )
    val clause_weights = Statistic( cweights )

    val stats = TstpProofStats( name, dagSize, treeSize, depth, hist.toMap, freq.toMap,
      fst_map_c( reused_axioms ), fst_map_c( reused_derived ), clause_sizes, clause_weights )

    stats
  }

}

