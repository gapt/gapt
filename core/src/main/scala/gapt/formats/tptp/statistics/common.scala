package gapt.formats.tptp

import ammonite.ops.FilePath
import gapt.formats.csv.CSVRow
import gapt.proofs.HOLSequent
import gapt.utils.Statistic

import scala.collection.mutable

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
  case class RPProofStats[T <: FileData](
      name:              T, // some class representing the input file
      dagSize:           BigInt,
      treeSize:          BigInt,
      depth:             Int,
      rule_histogram:    Map[RuleName, Int],
      clause_frequency:  Map[ClauseId, ( RuleName, Int )],
      subst_term_sizes:  Option[Statistic[Int]],
      subst_term_depths: Option[Statistic[Int]],
      reused_axioms:     Map[RuleName, ( HOLSequent, Int )],
      reused_derived:    Map[RuleName, ( HOLSequent, Int )],
      clause_sizes:      Statistic[Int] ) {

    def sizeRatio() = BigDecimal( treeSize ) / BigDecimal( dagSize )

    def reused_statistics() = Statistic( reused_axioms.toList.map( _._2._2 ) )

    def derived_statistics() = Statistic( reused_derived.toList.map( _._2._2 ) )

    def toCSV: CSVRow[String] = {
      val ( problem, solver ) = name match {
        case CASCResult( _, prover, problem, _ ) => ( prover, problem )
        case other                               => ( "unknown", other.fileName )
      }
      CSVRow( List( problem, solver, dagSize.toString, treeSize.toString, sizeRatio.toString,
        depth.toString ) )
    }
  }

  /*
    Companion object for RPProofSTats[T]
   */
  object RPProofStats {
    val csv_header = CSVRow( List( "problem", "solver", "dagsize", "treesize", "sizeratio", "depth" ) )
  }

  /*
   Invariants:
   dagSize <= treeSize
   dept <= size
 */
  case class TstpProofStats[T](
      name:             FileData,
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
      name:                FileData,
      axiom_count:         Int,
      input_formula_count: Int,
      signature_size:      Int,
      constants:           Int,
      unary_funs:          Int,
      binary_funs:         Int,
      max_arity:           Int,
      median_arity:        Int )

}
