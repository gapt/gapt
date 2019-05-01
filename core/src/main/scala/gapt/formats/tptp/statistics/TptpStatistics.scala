package gapt.formats.tptp.statistics

import ammonite.ops.FilePath
import gapt.expr._
import gapt.expr.ty.arity
import gapt.expr.util.constants
import gapt.formats.csv.CSVFile
import gapt.formats.csv.CSVRow
import gapt.formats.tptp.AnnotatedFormula
import gapt.formats.tptp.TptpFile
import gapt.formats.tptp.TptpFormulaRoles
import gapt.formats.tptp.TptpImporter
import gapt.utils.Statistic

import scala.collection.mutable

object TPTPstatistics {
  type Signature = Map[Int, Set[Const]]
  type Freqmap = Map[Const, Int]
  type Sigtable = Map[String, Seq[Set[Const]]]

  def apply[T <: TptpLibraryProblem]( name: T ): TptpInputStats[T] = {
    val tptpFile = TptpImporter.loadWithIncludes( name.file, f => TptpImporter.loadWithoutIncludes( FilePath( s"${name.path}/$f" ) ) )
    apply( tptpFile, name )
  }

  def apply[T <: FileData]( tptpFile: TptpFile, name: T = UnknownFile ): TptpInputStats[T] = {
    val ( deps, sequent ) = tptpFile.toSequentWithIncludes

    val formula_assertions = tptpFile.inputs.collect {
      case a @ AnnotatedFormula( language, name, role, formula, annotations ) if TptpFormulaRoles() contains role => a
    }

    val axiom_assertions = formula_assertions.filter( _.role == "axiom" )

    //get symbols in file
    val consts = constants( sequent )

    //compute frequency of arities
    val sig = mutable.Map[Int, Set[Const]]()
    for ( c <- consts ) {
      val ar = arity( c.ty )
      val entry = sig.getOrElse( ar, Set[Const]() )
      sig( ar ) = entry + c
    }

    val has_equality = constants.equalities( sequent.toFormula ).nonEmpty

    //compute arity statistics
    val arity_statistics = Statistic.applyOpt( consts.toList.map( c => arity( c.ty ) ) )
    arity_statistics match {
      case Some( Statistic( n, _, _, _, _, _ ) ) =>
        require( n == consts.size, "Number of constants must agree with n of arity statistics!" )
      case _ => ()
    }

    //compute frequency of constants
    val frequencies = mutable.Map[Const, Int]()
    for ( c <- consts ) {
      val entry = frequencies.getOrElse( c, 0 )
      frequencies( c ) = entry + 1
    }

    val const_count = sig.getOrElse( 0, Set() ).size
    val unary_count = sig.getOrElse( 1, Set() ).size
    val binary_count = sig.getOrElse( 2, Set() ).size
    val total_count = sig.values.flatten.foldLeft( 0 )( ( sum, c ) => sum + arity( c.ty ) )

    TptpInputStats( name, axiom_assertions.size, formula_assertions.size,
      total_count, const_count, unary_count, binary_count, has_equality, arity_statistics )

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
