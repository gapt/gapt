package gapt.formats.tptp

import ammonite.ops._
import gapt.formats.csv.{ CSVFile, CSVRow }
import gapt.utils.Statistic

package object statistics {

  type RuleName = String
  type ClauseId = String
  type Prover = String
  type Problem = String

  /**
   * Easier representation of file paths data follow a certain schema
   */
  abstract class FileData {
    def fileName: String

    def file = FilePath( fileName )
  }

  /**
    * A filename that comes from the CASC competition: the prover and TSTP problem name are accessible.
    * The filename is automatically set to $path/$prover-$problem$extension
    * @param path The problem path
    * @param prover The prover produceing the tstp file
    * @param problem The TSTP library problem (see http://www.cs.miami.edu/~tptp/cgi-bin/SystemOnTPTP?TPTPProblem=$problem )
    * @param extension The file extension
    */
  case class CASCResult( path: String, prover: Prover, problem: String, extension: String )
    extends FileData {
    def fileName = s"$path/$prover-$problem$extension"

    override def toString() = fileName

  }
  object CASCResult {
    def toCSV( r: CASCResult ) = CSVRow( List( r.fileName, r.prover, r.problem ) )

    val fileHeader = CSVRow( List( "Filename", "Prover", "Problem" ) )
  }
  /**
    * Statistical data for a [[gapt.proofs.resolution.ResolutionProof]] proof rp
    * @param name the name of the problem
    * @param dagSize the same as rp.dagSize
    * @param treeSize the same as rp.treeSize
    * @param depth the same as sketch.depth
    * @param rule_histogram map from a rule's name to how often the rule appears in the proof
    * @param clause_frequency a map from the clause id to how often the clause appears
    * @param subst_term_depths statistics about the term depths occurring in [[gapt.proofs.resolution.Subst]] rules
    * @param subst_term_sizes statistics about the term sizes occurring in [[gapt.proofs.resolution.Subst]] rules
    * @param reused_axioms the frequency of all leaf nodes that are used at least once
    * @param reused_derived the frequency of all inner nodes that are used at least once
    * @param clause_sizes statistics over the length of clauses in the proof
    * @tparam T a subtype of [[FileData]] that represents the location and metadata of a TSTP file
    */
  @SerialVersionUID( 70112L )
  case class RPProofStats[T <: FileData](
      name:              T, // some class representing the input file
      dagSize:           BigInt,
      treeSize:          BigInt,
      depth:             Int,
      rule_histogram:    Map[RuleName, Int],
      clause_frequency:  Map[ClauseId, ( RuleName, Int )],
      subst_term_sizes:  Option[Statistic[Int]],
      subst_term_depths: Option[Statistic[Int]],
      //      reused_axioms:     Map[RuleName, ( HOLSequent, Int )],
      //      reused_derived:    Map[RuleName, ( HOLSequent, Int )],
      reused_axioms:  Map[RuleName, ( String, Int )], //TODO: as soon as term serialization is ready, change back to sequents
      reused_derived: Map[RuleName, ( String, Int )],
      clause_sizes:   Statistic[Int] ) extends Serializable {
    /*
     Invariants:
     dagSize <= treeSize
     dept <= size
   */

    def sizeRatio() = BigDecimal( treeSize ) / BigDecimal( dagSize )

    def reused_statistics() = Statistic( reused_axioms.toList.map( _._2._2 ) )

    def derived_statistics() = Statistic( reused_derived.toList.map( _._2._2 ) )

    def csv_header() = RPProofStats.csv_header

    def toCSV: CSVRow[String] = {
      import RPProofStats._
      val ( problem, solver ) = name match {
        case CASCResult( _, prover, problem, _ ) => ( prover, problem )
        case other                               => ( "unknown", other.fileName )
      }
      CSVRow(
        List( problem, solver, dagSize.toString, treeSize.toString,
          sizeRatio.toString, depth.toString )
          ++ also_empty_stat_csv( rule_histogram.toList.map( _._2 ) )
          ++ statistic_opt_csv( subst_term_sizes )
          ++ statistic_opt_csv( subst_term_depths )
          ++ also_empty_stat_csv( reused_axioms.toList.map( _._2._2 ) )
          ++ also_empty_stat_csv( reused_derived.toList.map( _._2._2 ) )
          ++ clause_sizes.toCSV )
    }

    private val na_statistic = RPProofStats.na_statistic //for compatibility

  }

  /**
    Companion object for [[RPProofStats]]
   */
  object RPProofStats {

    /**
      * Static header for CSV export
      */
    val csv_header = CSVRow(
      List( "problem", "solver", "dagsize", "treesize", "sizeratio", "depth" )
        ++ Statistic.csv_header( "inference_freq" )
        ++ Statistic.csv_header( "subterm_size" )
        ++ Statistic.csv_header( "subterm_depth" )
        ++ Statistic.csv_header( "reused_axioms" )
        ++ Statistic.csv_header( "reused_derived" )
        ++ Statistic.csv_header( "clause_sizes" ) )

    /**
      * static "not applicable" CSV value for a non-existing statistic
      */
    val na_statistic = Statistic( 0 :: Nil ).toCSV map ( _ => "NA" )

    /**
      * Converts a statistic option to CSV with a default of not applicable
      * @param s an optional statistic
      * @tparam T the type of data elements of the statistic
      * @return CSV data for s, if it exists [[na_statistic]] otherwise
      */
    def statistic_opt_csv[T]( s: Option[Statistic[T]] ) = s match {
      case None                    => na_statistic
      case Some( s: Statistic[T] ) => s.toCSV
    }

    /**
      * Produces CSV data of statistics for non-empty data, and 'not applicable' values otherwise.
      * @param s a sequence of data
      * @param num the implicit converter to treat elements of s as numeric types
      * @param conv a measure for calculating the avarage and standard deviation in the statistic
      * @tparam T the type of data to create statistics on  (must be measurable in terms of num and conv)
      * @return CSV data for s if it is non-empty, [[na_statistic]] otherwise
      */
    def also_empty_stat_csv[T]( s: Seq[T] )( implicit num: Numeric[T], conv: T => BigDecimal ): Seq[String] =
      if ( s.isEmpty ) na_statistic else Statistic( s ).toCSV

    /**
      * Creates a [[CSVFile]] from a map of [[FileData]] problem files to
      * proof sketch [[TstpProofStats]] or resolution proof [[RPProofStats]] statistics.
      * @param m the map
      * @param sep the seperator for the CSV file
      * @tparam S the type of files
      * @tparam T either [[RPProofStats]] or [[TstpProofStats]]
      * @return a CSV File representing m
      */
    def toCSVFile[S <: FileData, T]( m: Map[S, T], sep: String = "," ) = {
      //TODO: refactor when RPPoofStats and TstpProofSTats inherit form a common class
      val entries = m.keySet.toSeq.sortBy( _.fileName )
      var header = CSVRow( List[String]() )
      val rows = entries.map( m.apply ).flatMap {
        case s: RPProofStats[_] =>
          header = RPProofStats.csv_header
          s.toCSV :: Nil
        case s: TstpProofStats[_] =>
          header = TstpProofStats.csv_header
          TstpProofStats.toCSV( s ) :: Nil
        case _ => Nil
      }
      CSVFile( header, rows, sep )

    }

  }

  /**
    * Statistical data for a [[gapt.proofs.sketch.RefutationSketch]] sketch
    * @param name the name of the problem
    * @param dagSize the same as sketch.dagSize
    * @param treeSize the same as sketch.treeSize
    * @param depth the same as sketch.depth
    * @param rule_histogram map from a rule's name to how often the rule appears in the proof
    * @param clause_frequency a map from the clause id to how often the clause appears
    * @param reused_axioms the frequency of all leaf nodes that are used at least once
    * @param reused_derived the frequency of all inner nodes that are used at least once
    * @param clause_sizes statistics over the length of clauses in the proof
    * @tparam T a subtype of [[FileData]] that represents the location and metadata of a TSTP file
    */
  //@SerialVersionUID( 70114L )
  case class TstpProofStats[T <: FileData](
      name:             T,
      dagSize:          BigInt,
      treeSize:         BigInt,
      depth:            Int,
      rule_histogram:   Map[RuleName, Int],
      clause_frequency: Map[ClauseId, ( RuleName, Int )],
      reused_axioms:    Map[RuleName, ( String, Int )],
      reused_derived:   Map[RuleName, ( String, Int )],
      clause_sizes:     Statistic[Int] ) extends Serializable {
    /*
     Invariants:
     dagSize <= treeSize
     dept <= size
   */
  }

  /**
    * Companion object for [[TstpProofStats]]
    */
  object TstpProofStats {
    val csv_header = CSVRow(
      List( "problem", "solver", "dagsize", "treesize", "sizeratio", "depth" )
        ++ Statistic.csv_header( "inference_freq" )
        ++ Statistic.csv_header( "reused_axioms" )
        ++ Statistic.csv_header( "reused_derived" )
        ++ Statistic.csv_header( "clause_sizes" ) )

    def sizeRatio[T <: FileData]( s: TstpProofStats[T] ) = BigDecimal( s.treeSize ) / BigDecimal( s.dagSize )

    def reused_statistics[T <: FileData]( s: TstpProofStats[T] ) = Statistic( s.reused_axioms.toList.map( _._2._2 ) )

    def derived_statistics[T <: FileData]( s: TstpProofStats[T] ) = Statistic( s.reused_derived.toList.map( _._2._2 ) )

    def toCSV[T <: FileData]( s: TstpProofStats[T] ): CSVRow[String] = {
      import RPProofStats._
      val TstpProofStats( name, dagSize, treeSize, depth, rule_histogram,
        _, reused_axioms, reused_derived, clause_sizes ) = s
      val ( problem, solver ) = name match {
        case CASCResult( _, prover, problem, _ ) => ( prover, problem )
        case other                               => ( "unknown", other.fileName )
      }
      CSVRow(
        List( problem, solver, dagSize.toString, treeSize.toString,
          sizeRatio( s ).toString, depth.toString )
          ++ also_empty_stat_csv( rule_histogram.toList.map( _._2 ) )
          ++ also_empty_stat_csv( reused_axioms.toList.map( _._2._2 ) )
          ++ also_empty_stat_csv( reused_derived.toList.map( _._2._2 ) )
          ++ clause_sizes.toCSV )
    }

    def toCSVFile[S <: FileData, T]( m: Map[S, T], sep: String = "," ) = RPProofStats.toCSVFile(m, sep)

  }

  /*
   Invariants:
    axiom_count <= input_formula_count
    constants + unary_funs + binary_funs <= signature_size
 */
  case class InputStats[T <: FileData](
      name:                T,
      axiom_count:         Int,
      input_formula_count: Int,
      signature_size:      Int,
      constants:           Int,
      unary_funs:          Int,
      binary_funs:         Int,
      max_arity:           Int,
      median_arity:        Int )


  /**
    * Collects errors and statistics from proof sketch and resolution proof reconstruction
    * @param tstp_stats the proof sketch statistics
    * @param rp_stats the resolution proof statistics
    * @param tstp_errors the proof sketch errors that occurred
    * @param rp_errors the replay errors that occurred
    * @tparam T the type of input files
    */
  @SerialVersionUID( 70113L )
  case class ResultBundle[T <: FileData](
      tstp_stats:  Map[T, TstpProofStats[T]],
      rp_stats:    Map[T, RPProofStats[T]],
      tstp_errors: List[TstpError[T]],
      rp_errors:   List[TstpError[T]] ) extends Serializable {
    def exportCSV( filename: String ) = {
      val f1 = TstpProofStats.toCSVFile( tstp_stats )
      val f2 = RPProofStats.toCSVFile( rp_stats )
      val f3 = CSVFile( CSVRow( Nil ), tstp_errors.map( TstpError.toCSV( _ ) ), "," )
      val f4 = CSVFile( CSVRow( Nil ), rp_errors.map( TstpError.toCSV( _ ) ), "," )

      write( Path( s"$filename-rp_stats.csv", pwd ), f1.toString() )
      write( Path( s"$filename-tstp_stats.csv", pwd ), f2.toString() )
      write( Path( s"$filename-rp_errors.csv", pwd ), f3.toString() )
      write( Path( s"$filename-tstp_errors.csv", pwd ), f4.toString() )
      ( f1, f2, f3, f4 )
    }
  }

}
