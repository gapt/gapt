package gapt.formats.tptp

import os.{ Path, _ }
import gapt.formats.{ InputFile, csv }
import gapt.formats.csv.{ CSVConvertible, CSVFile, CSVRow }
import gapt.utils.Statistic

package object statistics {

  type RuleName = String
  type ClauseId = String
  type Prover = String
  type Problem = String

  /**
   * Calculates [[RPProofStats]] for a given [[gapt.proofs.resolution.ResolutionProof]]
   *
   * @param name the file containing rp
   * @param rp   the replayed proof
   * @tparam T the instance of [[FileData]] describing the file name
   * @return proof statistic for rp
   */

  /**
   * Easier representation of file paths data follow a certain schema
   */
  abstract class FileData extends InputFile with Serializable with CSVConvertible[String] {
    override def fileName: String

    def read = os.read(fileAsPath)

    def file = FilePath( fileName )

    def fileAsPath: Path = makeAbsolutePath( file )

    private def makeAbsolutePath( relativePath: FilePath ): Path =
      Path( relativePath, pwd )
  }

  case object UnknownFile extends FileData {
    override def fileName: String = {
      throw new IllegalArgumentException( "File does not exist!" )
    }
    override def csvHeader(): CSVRow[String] = {
      throw new IllegalArgumentException( "File does not exist!" )
    }
    override def toCSV(): CSVRow[String] = {
      throw new IllegalArgumentException( "File does not exist!" )
    }
  }

  /**
   * Represents a TPTP library problem of a certain category. The problem must be in
   * \$path/Problems/XYZ/ - \$path/Axioms must contain the axiom files to include.
   *
   * @param path    the path to the TPTP base directory
   * @param problem a TPTP library problem
   */
  @SerialVersionUID( 7467907234480399719L )
  case class TptpLibraryProblem( path: String, problem: Problem ) extends FileData with Serializable {
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
    override def csvHeader(): CSVRow[String] = CSVRow( List( "problem" ) )
    override def toCSV(): CSVRow[String] = CSVRow( List( problem ) )
  }

  /**
   * A filename that comes from the CASC competition: the prover and TSTP problem name are accessible.
   * The filename is automatically set to \$path/\$prover-\$problem\$extension
   *
   * @param path      The problem path
   * @param prover    The prover produceing the tstp file
   * @param problem   The TSTP library problem (see http://www.cs.miami.edu/~tptp/cgi-bin/SystemOnTPTP?TPTPProblem=\$problem )
   * @param extension The file extension
   */
  case class CASCResult( path: String, prover: Prover, problem: String, extension: String ) extends FileData with Serializable {
    def fileName = s"$path/$prover-$problem$extension"

    override def toString() = fileName

    override def csvHeader(): CSVRow[String] = CSVRow( List( "prover", "problem" ) )
    override def toCSV(): CSVRow[String] = CSVRow( List( prover, problem ) )
  }

  object CASCResult {
    def toCSV( r: CASCResult ) = CSVRow( List( r.fileName, r.prover, r.problem ) )

    val fileHeader = CSVRow( List( "Filename", "Prover", "Problem" ) )
  }

  /**
   * Statistical data for a [[gapt.proofs.resolution.ResolutionProof]] proof rp
   *
   * @param name              the name of the problem
   * @param dagSize           the same as rp.dagSize
   * @param treeSize          the same as rp.treeSize
   * @param depth             the same as sketch.depth
   * @param rule_histogram    map from a rule's name to how often the rule appears in the proof
   * @param clause_frequency  a map from the clause id to how often the clause appears
   * @param subst_term_depths statistics about the term depths occurring in [[gapt.proofs.resolution.Subst]] rules
   * @param subst_term_sizes  statistics about the term sizes occurring in [[gapt.proofs.resolution.Subst]] rules
   * @param reused_axioms     the frequency of all leaf nodes that are used at least once
   * @param reused_derived    the frequency of all inner nodes that are used at least once
   * @param clause_sizes      statistics over the length of clauses in the proof
   * @tparam T a subtype of [[FileData]] that represents the location and metadata of a TSTP file
   */
  @SerialVersionUID( -2181096749132376641L )
  abstract class CommonProofStats[T <: FileData](
      val name:             T,
      val dagSize:          BigInt,
      val treeSize:         BigInt,
      val depth:            Int,
      val rule_histogram:   Map[RuleName, Int],
      val clause_frequency: Map[ClauseId, Int],
      val reused_axioms:    Map[RuleName, ( String, Int )], //TODO: change String type back to HOLSequent
      val reused_derived:   Map[RuleName, ( String, Int )],
      val clause_sizes:     Statistic[Int],
      val clause_weights:   Statistic[Int] ) extends Serializable with CSVConvertible[String] {
    /*
      Invariants:
      dagSize <= treeSize
      depth <= size
    */

    /**
     * Computes treeSize / dagSize
     */
    def sizeRatio() = BigDecimal( treeSize ) / BigDecimal( dagSize )

    /**
     * Computes dagSize / depth
     */
    def dagSizeByDepth() = BigDecimal( dagSize ) / BigDecimal( depth )

    /**
     * Computes statistics how often axioms are reused
     */
    def reused_statistics() = Statistic.applyOpt( reused_axioms.toList.map( _._2._2 ) )

    /**
     * Computes statistics how often derived axioms are reused
     */
    def derived_statistics() = Statistic.applyOpt( reused_derived.toList.map( _._2._2 ) )

  }

  /**
   * Statistical data for a [[gapt.proofs.resolution.ResolutionProof]] proof rp
   *
   * @param name              the name of the problem
   * @param dagSize           the same as rp.dagSize
   * @param treeSize          the same as rp.treeSize
   * @param depth             the same as sketch.depth
   * @param rule_histogram    map from a rule's name to how often the rule appears in the proof
   * @param clause_frequency  a map from the clause id to how often the clause appears
   * @param subst_term_depths statistics about the term depths occurring in [[gapt.proofs.resolution.Subst]] rules
   * @param subst_term_sizes  statistics about the term sizes occurring in [[gapt.proofs.resolution.Subst]] rules
   * @param reused_axioms     the frequency of all leaf nodes that are used at least once
   * @param reused_derived    the frequency of all inner nodes that are used at least once
   * @param clause_sizes      statistics over the length of clauses in the proof
   * @tparam T a subtype of [[FileData]] that represents the location and metadata of a TSTP file
   */
  @SerialVersionUID( 80112L )
  case class RPProofStats[T <: FileData](
      override val name:             T, // some class representing the input file
      override val dagSize:          BigInt,
      override val treeSize:         BigInt,
      override val depth:            Int,
      override val rule_histogram:   Map[RuleName, Int],
      override val clause_frequency: Map[ClauseId, Int],
      override val reused_axioms:    Map[RuleName, ( String, Int )], //TODO: change String type back to HOLSequent
      override val reused_derived:   Map[RuleName, ( String, Int )],
      override val clause_sizes:     Statistic[Int],
      override val clause_weights:   Statistic[Int],
      val subst_term_sizes:          Option[Statistic[Int]],
      val subst_term_depths:         Option[Statistic[Int]] )
    extends CommonProofStats[T]( name, dagSize, treeSize, depth, rule_histogram, clause_frequency,
      reused_axioms, reused_derived, clause_sizes, clause_weights )
    with Serializable {

    override def csvHeader() = RPProofStats.csv_header

    override def toCSV(): CSVRow[String] = {
      val ( problem, solver ) = name match {
        case CASCResult( _, prover, problem, _ ) => ( prover, problem )
        case other                               => ( "unknown", other.fileName )
      }
      CSVRow(
        List( problem, solver, dagSize.toString(), treeSize.toString(),
          sizeRatio().toString(), depth.toString() )
          ++ Statistic.alsoEmptyDataToCSV( clause_frequency.toList.map( _._2 ) )
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
      List( "solver", "problem", "dagsize", "treesize", "sizeratio", "depth" )
        ++ Statistic.csv_header( "inference_freq" )
        ++ Statistic.csv_header( "rules_freq" )
        ++ Statistic.csv_header( "subterm_size" )
        ++ Statistic.csv_header( "subterm_depth" )
        ++ Statistic.csv_header( "reused_axioms" )
        ++ Statistic.csv_header( "reused_derived" )
        ++ Statistic.csv_header( "clause_sizes" ) )

    /**
     * Creates a `CSVFile` from a map of [[FileData]] problem files to
     * proof sketch [[TstpProofStats]] or resolution proof [[RPProofStats]] statistics.
     *
     * @param m   the map
     * @param sep the seperator for the CSV file
     * @tparam S the type of files
     * @tparam T either [[RPProofStats]] or [[TstpProofStats]]
     * @return a CSV File representing m
     */
    def toCSVFile[S <: FileData, T <: CSVConvertible[String]]( m: Map[S, T], sep: String = "," ) = {
      val entries = m.keySet.toSeq.sortBy( _.fileName )
      val rows = entries.map( m.apply ).map( _.toCSV() )

      var header = if ( entries.nonEmpty ) m( entries( 0 ) ).csvHeader() else CSVRow( List[String]() )

      CSVFile( header, rows, sep )
    }

  }

  /**
   * Statistical data for a [[gapt.proofs.sketch.RefutationSketch]] sketch
   *
   * @param name             the name of the problem
   * @param dagSize          the same as sketch.dagSize
   * @param treeSize         the same as sketch.treeSize
   * @param depth            the same as sketch.depth
   * @param rule_histogram   map from a rule's name to how often the rule appears in the proof
   * @param clause_frequency a map from the clause id to how often the clause appears
   * @param reused_axioms    the frequency of all leaf nodes that are used at least once
   * @param reused_derived   the frequency of all inner nodes that are used at least once
   * @param clause_sizes     statistics over the length of clauses in the proof
   * @tparam T a subtype of [[FileData]] that represents the location and metadata of a TSTP file
   */
  //@SerialVersionUID( 80114L )
  @SerialVersionUID( 833764725943944297L )
  case class TstpProofStats[T <: FileData](
      override val name:             T,
      override val dagSize:          BigInt,
      override val treeSize:         BigInt,
      override val depth:            Int,
      override val rule_histogram:   Map[RuleName, Int],
      override val clause_frequency: Map[ClauseId, Int],
      override val reused_axioms:    Map[RuleName, ( String, Int )],
      override val reused_derived:   Map[RuleName, ( String, Int )],
      override val clause_sizes:     Statistic[Int],
      override val clause_weights:   Statistic[Int] )
    extends CommonProofStats[T]( name, dagSize, treeSize, depth, rule_histogram, clause_frequency,
      reused_axioms, reused_derived, clause_sizes, clause_weights )
    with Serializable {

    override def csvHeader() = TstpProofStats.csv_header
    override def toCSV(): CSVRow[String] = {
      val ( problem, solver ) = name match {
        case CASCResult( _, prover, problem, _ ) => ( prover, problem )
        case other                               => ( "unknown", other.fileName )
      }
      CSVRow(
        List( problem, solver, dagSize.toString(), treeSize.toString(),
          sizeRatio().toString(), depth.toString() )
          ++ Statistic.alsoEmptyDataToCSV( clause_frequency.toList.map( _._2 ) )
          ++ Statistic.alsoEmptyDataToCSV( rule_histogram.toList.map( _._2 ) )
          ++ Statistic.alsoEmptyDataToCSV( reused_axioms.toList.map( _._2._2 ) )
          ++ Statistic.alsoEmptyDataToCSV( reused_derived.toList.map( _._2._2 ) )
          ++ clause_sizes.toCSV )
    }

  }

  /**
   * Companion object for [[TstpProofStats]]
   */
  object TstpProofStats {
    val csv_header = CSVRow(
      List( "solver", "problem", "dagsize", "treesize", "sizeratio", "depth" )
        ++ Statistic.csv_header( "inference_freq" )
        ++ Statistic.csv_header( "rules_freq" )
        ++ Statistic.csv_header( "reused_axioms" )
        ++ Statistic.csv_header( "reused_derived" )
        ++ Statistic.csv_header( "clause_sizes" ) )

    def toCSVFile[S <: FileData, T <: CSVConvertible[String]]( m: Map[S, T], sep: String = "," ) =
      RPProofStats.toCSVFile( m, sep )
  }

  /**
   * Captures data from a TPTP problem file
   *
   * @param name                the file the data comes from
   * @param axiom_count         the number of axioms in the problem (including included files)
   * @param input_formula_count the number statements asserting an imput formula
   * @param signature_size      the total number of different constants and function symbols
   * @param constants           the number of constants in the problem
   * @param unary_funs          the number of unary functions in the problem
   * @param binary_funs         the number of binary functions in the problem
   * @param arity_statistics    statistical data about the arities of function symbols (may be empty e.g. for ∀xEy.x=y)
   * @tparam T
   */
  @SerialVersionUID( -2646726266696413930L )
  case class TptpInputStats[T <: FileData](
      name:                T,
      axiom_count:         Int,
      input_formula_count: Int,
      signature_size:      Int,
      constants:           Int,
      unary_funs:          Int,
      binary_funs:         Int,
      contains_equality:   Boolean,
      arity_statistics:    Option[Statistic[Int]] )
    extends CSVConvertible[String] {
    /*
     Invariants:
      axiom_count <= input_formula_count
      constants + unary_funs + binary_funs <= signature_size
   */
    override def csvHeader() =
      name.csvHeader() ++ csv.CSVRow(
        List( "axiom_count", "input_formula_count", //signature size is contained in arity statisticis
          "constants", "unary_funs", "binary_funs" )
          ++ Statistic.csv_header( "arities" ) )

    override def toCSV() = {
      val namecol = name.toCSV()

      namecol ++ CSVRow(
        List( axiom_count, input_formula_count, constants, unary_funs, binary_funs ).map( _.toString() ) ++
          Statistic.optCSV( arity_statistics ) //arity_statistics contains the signature size
      )
    }
  }

  /**
   * Collects errors and statistics from proof sketch and resolution proof reconstruction
   *
   * @param tstp_stats  the proof sketch statistics
   * @param rp_stats    the resolution proof statistics
   * @param tstp_errors the proof sketch errors that occurred
   * @param rp_errors   the replay errors that occurred
   * @tparam T the type of input files
   */
  @SerialVersionUID( 70113L )
  case class ResultBundle[T <: FileData](
      tstp_stats:  Map[T, TstpProofStats[T]],
      rp_stats:    Map[T, RPProofStats[T]],
      tstp_errors: List[TstpError[T]],
      rp_errors:   List[TstpError[T]] ) extends Serializable {

    /**
     * Write a bundle to a set of files: \$file_prefix-rp-stats.csv, \$file_prefix-tstp-stats.csv,
     * \$file_prefix-rp-errors.csv and \$file_prefix-tstp-errors.csv
     *
     * @param file_prefix the prefix for the files
     * @param path        the path where to save the file, default : pwd
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
