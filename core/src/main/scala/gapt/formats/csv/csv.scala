package gapt.formats.csv

/**
 * Represents one row in a csv file
 * @param cells the content of each column
 * @tparam T the type of cells
 */
case class CSVRow[T]( cells: Seq[T] ) {
  /**
   * Appends the given row to this row's columns
   * @param row
   * @return
   */
  def ++( row: CSVRow[T] ) = CSVRow( cells ++ row.cells )
}

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

  /**
   * Adds given file as columns right of the current ones
   * @param file
   * @return the file with the extended rows and header
   */
  def ++( file: CSVFile[T] ) = {
    require( file.sep == sep, "can only merge csv files with the same seperator" )
    require( file.rows.size == rows.size, "can only merge csv files with same numebr of rows" )
    CSVFile( header ++ file.header, ( rows zip file.rows ).map { case ( x, y ) => x ++ y }, sep )
  }

}

object CSVFile {
  val defaultSep = ", "
}
