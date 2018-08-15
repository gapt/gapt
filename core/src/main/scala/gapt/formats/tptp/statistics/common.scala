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
   * Calculates [[RPProofStats]] for a given [[gapt.proofs.resolution.ResolutionProof]]
   * @param name the file containing rp
   * @param rp the replayed proof
   * @tparam T the instance of [[FileData]] describing the file name
   * @return proof statistic for rp
   */

  /**
   * Easier representation of file paths data follow a certain schema
   */
  abstract class FileData {
    def fileName: String

    def file = FilePath( fileName )
  }

  case object UnknownFile extends FileData {
    override def fileName: String = { throw new IllegalArgumentException( "File does not exist!" ) }
  }

  /**
   * Represents a TPTP library problem of a certain category. The problem must be in
   * $path/Problems/XYZ/ - $path/Axioms must contain the axiom files to include.
   * @param path the path to the TPTP base directory
   * @param problem a TPTP library problem
   */
  case class TptpLibraryProblem( path: String, problem: Problem ) extends FileData {
    /**
     * The category is encoded in the file name
     */
    val category = categoryOfFile( problem )

    /**
     * Extracts the category from the file name i.e. the first 3 letters
     */
    def categoryOfFile( f: String ) = {
      require( f.size > 3, "Name must be larger than 3 characters." )
      f take 3
    }

    override def fileName = s"$path/Problems/$category/$problem.p"
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
     depth <= size
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
          ++ Statistic.alsoEmptyDataToCSV( rule_histogram.toList.map( _._2 ) )
          ++ Statistic.optCSV( subst_term_sizes )
          ++ Statistic.optCSV( subst_term_depths )
          ++ Statistic.alsoEmptyDataToCSV( reused_axioms.toList.map( _._2._2 ) )
          ++ Statistic.alsoEmptyDataToCSV( reused_derived.toList.map( _._2._2 ) )
          ++ clause_sizes.toCSV )
    }

  }

  /**
   * Companion object for [[RPProofStats]]
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
          ++ Statistic.alsoEmptyDataToCSV( rule_histogram.toList.map( _._2 ) )
          ++ Statistic.alsoEmptyDataToCSV( reused_axioms.toList.map( _._2._2 ) )
          ++ Statistic.alsoEmptyDataToCSV( reused_derived.toList.map( _._2._2 ) )
          ++ clause_sizes.toCSV )
    }

    def toCSVFile[S <: FileData, T]( m: Map[S, T], sep: String = "," ) = RPProofStats.toCSVFile( m, sep )

  }

  /**
   * Captures data from a TPTP problem file
   * @param name the file the data comes from
   * @param axiom_count the number of axioms in the problem (including included files)
   * @param input_formula_count the number statements asserting an imput formula
   * @param signature_size the total number of different constants and function symbols
   * @param constants the number of constants in the problem
   * @param unary_funs the number of unary functions in the problem
   * @param binary_funs the number of binary functions in the problem
   * @param arity_statistics statistical data about the arities of function symbols (may be empty e.g. for ∀xEy.x=y)
   * @tparam T
   */
  case class TptpInputStats[T <: FileData](
      name:                T,
      axiom_count:         Int,
      input_formula_count: Int,
      signature_size:      Int,
      constants:           Int,
      unary_funs:          Int,
      binary_funs:         Int,
      contains_equality:   Boolean,
      arity_statistics:    Option[Statistic[Int]] ) {
    /*
     Invariants:
      axiom_count <= input_formula_count
      constants + unary_funs + binary_funs <= signature_size
   */
  }
  object TptpInputStats {
    def csv_header = List( "problem", "axiom_count", "input_formula_count", //signature size is contained in arity statisticis
      "constants", "unary_funs", "binary_funs" ) ++ Statistic.csv_header( "arities" ) //TODO: fix this for arbitrary file data, this only works for TptpLibraryProblem atm
    def toCSV[T <: FileData]( s: TptpInputStats[T] ) = {
      val namecol = s.name match {
        case CASCResult( path, prover, problem, extension ) =>
          List( prover, problem )
        case TptpLibraryProblem( path, problem ) =>
          List( problem )
      }

      CSVRow( namecol ++
        List( s.axiom_count, s.input_formula_count, s.constants, s.unary_funs, s.binary_funs ).map( _.toString ) ++
        Statistic.optCSV( s.arity_statistics ) //arity_statistics contains the signature size
      )
    }
  }

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

    /**
     * Write a bundle to a set of files: $file_prefix-rp-stats.csv, $file_prefix-tstp-stats.csv,
     * $file_prefix-rp-errors.csv and $file_prefix-tstp-errors.csv
     * @param file_prefix the prefix for the files
     * @param path the path where to save the file, default : pwd
     * @return the csv files written to disk
     */
    def exportCSV( file_prefix: String, path: Path = pwd ) = {
      val f1 = TstpProofStats.toCSVFile( tstp_stats )
      val f2 = RPProofStats.toCSVFile( rp_stats )
      val f3 = CSVFile( CSVRow( Nil ), tstp_errors.map( TstpError.toCSV( _ ) ), "," )
      val f4 = CSVFile( CSVRow( Nil ), rp_errors.map( TstpError.toCSV( _ ) ), "," )

      write( Path( s"${file_prefix}-rp_stats.csv", path ), f1.toString() )
      write( Path( s"${file_prefix}-tstp_stats.csv", path ), f2.toString() )
      write( Path( s"${file_prefix}-rp_errors.csv", path ), f3.toString() )
      write( Path( s"${file_prefix}-tstp_errors.csv", path ), f4.toString() )
      ( f1, f2, f3, f4 )
    }
  }

}
