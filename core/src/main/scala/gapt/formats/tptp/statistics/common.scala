package gapt.formats.tptp

import ammonite.ops.FilePath
import gapt.formats.csv.CSVRow
import gapt.proofs.HOLSequent
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

  case class CASCResult( path: String, prover: Prover, problem: String, extension: String )
    extends FileData {
    def fileName = s"$path/$prover-$problem$extension"

    override def toString() = fileName
  }

  /*
   Invariants:
   dagSize <= treeSize
   dept <= size
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
      reused_axioms:  Map[RuleName, ( String, Int )],
      reused_derived: Map[RuleName, ( String, Int )],
      clause_sizes:   Statistic[Int] ) extends Serializable {

    def sizeRatio() = BigDecimal( treeSize ) / BigDecimal( dagSize )

    def reused_statistics() = Statistic( reused_axioms.toList.map( _._2._2 ) )

    def derived_statistics() = Statistic( reused_derived.toList.map( _._2._2 ) )

    def toCSV: CSVRow[String] = {
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

    private val na_statistic = Statistic( 0 :: Nil ).toCSV map ( _ => "NA" )

    private def statistic_opt_csv[T]( s: Option[Statistic[T]] ) = s match {
      case None                    => na_statistic
      case Some( s: Statistic[T] ) => s.toCSV
    }
    private def also_empty_stat_csv[T]( s: Seq[T] )( implicit num: Numeric[T], conv: T => BigDecimal ): Seq[String] =
      if ( s.isEmpty ) na_statistic else Statistic( s ).toCSV

  }

  /*
    Companion object for RPProofSTats[T]
   */
  object RPProofStats {
    val csv_header = CSVRow(
      List( "problem", "solver", "dagsize", "treesize", "sizeratio", "depth" )
        ++ Statistic.csv_header( "inference_freq" )
        ++ Statistic.csv_header( "subterm_size" )
        ++ Statistic.csv_header( "subterm_depth" )
        ++ Statistic.csv_header( "reused_axioms" )
        ++ Statistic.csv_header( "reused_derived" )
        ++ Statistic.csv_header( "clause_sizes" ) )
  }

  /*
   Invariants:
   dagSize <= treeSize
   dept <= size
 */
  case class TstpProofStats[T <: FileData](
      name:             T,
      dagSize:          BigInt,
      treeSize:         BigInt,
      depth:            Int,
      rule_histogram:   Map[RuleName, Int],
      clause_frequency: Map[ClauseId, ( RuleName, Int )],
      reused_axioms:    Map[RuleName, ( String, Int )],
      reused_derived:   Map[RuleName, ( String, Int )],
      clause_sizes:     Statistic[Int] ) extends Serializable

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

  @SerialVersionUID( 70113L )
  case class ResultBundle[T <: FileData](
      tstp_stats:  Map[T, TstpProofStats[T]],
      rp_stats:    Map[T, RPProofStats[T]],
      tstp_errors: List[TstpError[T]],
      rp_errors:   List[TstpError[T]] ) extends Serializable

}
