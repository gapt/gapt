/** 
 * Description: 
**/

package at.logic.cli

import at.logic.transformations.ceres.struct.StructCreators
import at.logic.transformations.ceres.clauseSets.StandardClauseSet

import at.logic.parsing.language.xml.XMLParser._
import at.logic.parsing.readers.XMLReaders._
import at.logic.algorithms.lk.simplification._
import at.logic.algorithms.lk.statistics._
import at.logic.algorithms.lk._
import at.logic.parsing.calculus.xml.saveXML

import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.algorithms.lk.simplification._
import at.logic.algorithms.lk._
import at.logic.transformations.skolemization.lksk.LKtoLKskc

import java.util.zip.GZIPInputStream
import java.io.{FileReader, FileInputStream, InputStreamReader}
import java.io.File.separator

object CommandLine {
  def main(args: Array[String]) {
      if ( args.length != 2 )
      {
        println ( "USAGE: ceres2 in.xml out.xml" )
        return -1;
      }

      val in_file = args(0)
      val out_file = args(1)

      val proofs = (new XMLReader(new InputStreamReader(new FileInputStream(in_file))) with XMLProofDatabaseParser).getProofs()
      if ( proofs.size != 1 )
      { 
        println( in_file + " must not contain more than one proof!" )
        return -1;
      }

      val proof = proofs.first
      printStats( proof )
      val proof_reg = regularize( proof )._1
      val proof_sk = LKtoLKskc( proof_reg )
      val s = StructCreators.extract( proof_sk )
      val cs = StandardClauseSet.transformStructToClauseSet( s )
      val dcs = deleteTautologies( cs )
      val css = setNormalize( dcs )
      println("css size: " + css.size )
      Runtime.getRuntime().gc();
      saveXML( Pair("css", (css.toList))::Nil, out_file )
      return 0
    }

  def sequentToString( s: Sequent ) = {
    var ret = ""
    s.antecedent.foreach( formula => ret += formula.toStringSimple + ", ")
    ret += " :- "
    s.succedent.foreach( formula => ret += formula.toStringSimple + ", ")
    ret
  }

  def printStats( p: LKProof ) = {
    val stats = getStatistics( p )
    print("unary: " + stats.unary + "\n")
    print("binary: " + stats.binary + "\n")
    print("cuts: " + stats.cuts + "\n")
  }
}
