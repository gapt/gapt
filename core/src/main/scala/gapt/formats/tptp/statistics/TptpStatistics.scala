package gapt.formats.tptp.statistics

import ammonite.ops.{ FilePath, Path, read }
import gapt.expr._
import gapt.formats.csv.{ CSVFile, CSVRow }
import gapt.formats.tptp.{ TptpFile, TptpParser }

import scala.collection.mutable

object TPTPstatistics {
  type Signature = Map[Int, Set[Const]]
  type Freqmap = Map[Const, Int]
  type Sigtable = Map[String, Seq[Set[Const]]]

  def apply( tptpFile: TptpFile ): ( Signature, Freqmap ) = {
    val ( deps, sequent ) = tptpFile.toSequentWithIncludes

    //get symbols in file
    val consts = constants( sequent ) // collect( Seq( sequent.toFormula ), Seq() )

    //compute frequency of arities
    val sig = mutable.Map[Int, Set[Const]]()
    for ( c <- consts ) {
      val ar = arity( c.ty )
      val entry = sig.getOrElse( ar, Set[Const]() )
      sig( ar ) = entry + c
    }

    //compute frequency of constants
    val frequencies = mutable.Map[Const, Int]()
    for ( c <- consts ) {
      val entry = frequencies.getOrElse( c, 0 )
      frequencies( c ) = entry + 1
    }

    ( sig.toMap, frequencies.toMap )

  }

  def apply( file_list: Path ): Sigtable = {
    val files = read.lines( file_list )

    val stats_per_file = mutable.Map[String, Signature]()
    var max_arity = 0

    for ( f <- files ) {
      println( s"processing $f" )
      val tptp_file = TptpParser.parse( FilePath( f ) )
      val ( sig, freq ) = apply( tptp_file )
      val mks = sig.keySet.max
      if ( mks > max_arity ) max_arity = mks
      stats_per_file( f ) = sig
    }

    val sig_table = stats_per_file.map( kv => {
      val ( name, sig ) = kv
      val row = for ( i <- Range( 0, max_arity ) ) yield {
        sig.get( i ) match {
          case None      => Set[Const]()
          case Some( s ) => s
        }
      }
      ( name, row )
    } )

    sig_table.toMap
  }

  def sigtableToCsv( table: Sigtable ): CSVFile[String] = {
    var cols = 0
    val rows = for ( ( fn, freqs ) <- table ) yield {
      if ( freqs.size > cols ) cols = freqs.size
      CSVRow( fn +: freqs.map( _.size.toString() ) )
    }

    val colnames = Range( 0, cols ).map( _.toString() )
    val header = CSVRow( "file" +: colnames )

    CSVFile( header, rows.toSeq, ", " )

  }

  def print( sig: Signature, freq: Freqmap ) = {
    println( "\"arity\", \"frequency\"" )
    for ( ar <- sig.keySet.toSeq.sorted ) {
      val set = sig( ar )
      println( s"$ar, ${set.size}" )
    }
    println()

    println( "\"constant\",\"arity\", \"frequency\"" )
    for ( ( Const( name, ty, _ ), f ) <- freq ) {
      val ar = arity( ty )
      println( s"$name, $ar, $f" )
    }
  }

}
