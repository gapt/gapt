package gapt.formats.csv

/**
 * Represents one row in a csv file
 * @param cells the content of each column
 * @tparam T the type of cells
 */
case class CSVRow[T]( cells: Seq[T] )

/**
 * Represents a csv file with a header
 * @param header the header row
 * @param rows the data rows
 * @param sep the column seprator
 * @tparam T the cell type
 */
case class CSVFile[T]( header: CSVRow[T], rows: Seq[CSVRow[T]], sep: String ) {

  override def toString(): String = {
    val sb = StringBuilder.newBuilder
    sb.append( header.cells.mkString( "", sep, "\n" ) )
    for ( r <- rows ) {
      sb.append( r.cells.mkString( "", sep, "\n" ) )
    }
    sb.toString()
  }

}

object CSVFile {
  val defaultSep = ", "
}
