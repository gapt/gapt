package at.logic.gapt.formats.tptp

import ammonite.ops.{ FilePath, Path, read }
import at.logic.gapt.expr._
import at.logic.gapt.formats.tptp.csv.{ CSVFile, CSVRow }

import scala.collection.mutable

package csv {
  case class CSVRow[T]( cells: Seq[T] );

  case class CSVFile[T]( header: CSVRow[T], rows: Seq[CSVRow[T]], sep: String ) {
    val defaultSep = ", "

    override def toString(): String = {
      val sb = StringBuilder.newBuilder
      sb.append( header.cells.mkString( "", sep, "\n" ) )
      for ( r <- rows ) {
        sb.append( r.cells.mkString( "", sep, "\n" ) )
      }
      sb.toString()
    }

  }

}

object TPTPstatistics {
  type signature = Map[Int, Set[Const]]
  type freqmap = Map[Const, Int]
  type sigtable = Map[String, Seq[Set[Const]]]

  def apply( tptpFile: TptpFile ): ( signature, freqmap ) = {
    val ( deps, sequent ) = tptpFile.toSequentWithIncludes

    //get symbols in file
    val consts = collect( Seq( sequent.toFormula ), Seq() )

    //compute frequency of arities
    val sig = mutable.Map[Int, Set[Const]]()
    for ( c <- consts ) {
      val ar = arity( c.ty, 0 )
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

  def apply( file_list: Path ): sigtable = {
    val files = read.lines( file_list )

    val stats_per_file = mutable.Map[String, signature]()
    var max_arity = 0

    for ( f <- files ) {
      println( s"processing $f" )
      val tptp_file = TptpParser.parse( FilePath( f ) )
      val ( sig, freq ) = apply( tptp_file )
      val mks = max( sig.keySet )
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

  def sigtableToCsv( table: sigtable ): CSVFile[String] = {
    var cols = 0
    val rows = for ( ( fn, freqs ) <- table ) yield {
      if ( freqs.size > cols ) cols = freqs.size
      CSVRow( fn +: freqs.map( _.size.toString() ) )
    }

    val colnames = Range( 0, cols ).map( _.toString() )
    val header = CSVRow( "file" +: colnames )

    CSVFile( header, rows.toSeq, ", " )

  }

  private def max( it: Iterable[Int] ) = {
    var m = 0
    for ( i <- it ) { if ( i > m ) m = i }
    m
  }

  def print( sig: signature, freq: freqmap ) = {
    println( "\"arity\", \"frequency\"" )
    for ( ar <- sig.keySet.toSeq.sorted ) {
      val set = sig( ar )
      println( s"$ar, ${set.size}" )
    }
    println()

    println( "\"constant\",\"arity\", \"frequency\"" )
    for ( ( Const( name, ty, _ ), f ) <- freq ) {
      val ar = arity( ty, 0 )
      println( s"$name, $ar, $f" )
    }
  }

  def arity( ty: Ty, acc: Int ): Int = ty match {
    case _ ->: t2 =>
      arity( t2, acc + 1 )
    case _ => acc
  }

  //we need a stack here to stay tail recursive
  def collect( stack: Seq[Expr], consts: Seq[Const] ): Seq[Const] =
    if ( stack.isEmpty ) consts
    else {
      val e = stack.head
      e match {
        case c @ NonLogicalConstant( _, _, _ ) =>
          collect( stack.tail, c +: consts )
        case c @ Const( _, _, _ ) => // don't add logical constants
          collect( stack.tail, consts )
        case Var( _, _ ) =>
          collect( stack.tail, consts )
        case Abs( x, t ) => collect( t +: stack.tail, consts )
        case App( s, t ) =>
          collect( s +: t +: stack.tail, consts )
      }
    }

}
