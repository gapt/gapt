package at.logic.gapt.provers.maxsat

import java.io._

import at.logic.gapt.expr.fol.TseitinCNF
import at.logic.gapt.formats.dimacs._
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol._
import at.logic.gapt.models.{ MapBasedInterpretation, Interpretation }
import at.logic.gapt.proofs.HOLClause
import at.logic.gapt.utils.logging.{ metrics, Logger, Stopwatch }
import at.logic.gapt.utils.traits.ExternalProgram
import at.logic.gapt.utils.{ withTempFile, runProcess }

import scala.collection.immutable.Map

/**
 * Solver for Weighted Partial MaxSAT problems.
 */
abstract class MaxSATSolver {

  /**
   * Solves a weighted partial MaxSAT problem.
   *
   * @param hard Hard constraints in CNF.
   * @param soft Soft constraints in CNF along with their weights.
   * @return None if hard is unsatisfiable, otherwise Some(model), where model is a model
   * of hard maximizing the sum of the weights of soft.
   */
  def solve( hard: DIMACS.CNF, soft: Seq[( DIMACS.Clause, Int )] ): Option[DIMACS.Model]

  def solve( hard: TraversableOnce[HOLClause], soft: TraversableOnce[( HOLClause, Int )] ): Option[Interpretation] = {
    val encoding = new DIMACSEncoding
    solve(
      encoding.encodeCNF( hard ),
      soft map { case ( clause, weight ) => encoding.encodeClause( clause ) -> weight } toSeq
    ) map { dimacsModel =>
        encoding.decodeModel( dimacsModel )
      }
  }

  /**
   * @param hard Hard constraints.
   * @param soft Soft constraints along with their weights.
   * @return None if hard is unsatisfiable, otherwise Some(model), where model is a model
   * of hard maximizing the sum of the weights of soft.
   */
  def solve( hard: HOLFormula, soft: TraversableOnce[( HOLFormula, Int )] ): Option[Interpretation] = {
    solve(
      metrics.time( "tseitin" ) { TseitinCNF( hard.asInstanceOf[FOLFormula] ) },
      soft.map( s => CNFp.toClauseList( s._1 ).map( f => ( f, s._2 ) ) ).flatten
    )
  }
}

abstract class ExternalMaxSATSolver extends MaxSATSolver with ExternalProgram {
  def command: Seq[String]

  protected def runProgram( dimacsInput: String ): String =
    withTempFile.fromString( dimacsInput ) { inFile =>
      runProcess.withExitValue( command :+ inFile )._2
    }

  def solve( hard: DIMACS.CNF, soft: Seq[( DIMACS.Clause, Int )] ): Option[DIMACS.Model] =
    readWDIMACS( runProgram( writeWDIMACS( hard, soft ) ) )

  val isInstalled =
    try solve( FOLAtom( "p" ), Seq( -FOLAtom( "p" ) -> 10 ) ).isDefined
    catch { case _: IOException => false }
}

class WDIMACSHelper( val hard: List[HOLClause], val soft: List[( HOLClause, Int )] )
    extends DIMACSHelper( hard ++ soft.map( _._1 ) ) {
  /**
   * Returns for a given atom and
   * polarization a String for a propositional Variable in .wcnf format
   * @param atom atom to provide
   * @param pol polarization (true, false)
   * @return a literal in .wcnf format
   */
  protected def getWCNFString( atom: FOLAtom, pol: Boolean, atom_map: Map[HOLAtom, Int] ): String =
    if ( pol ) atom_map.get( atom ).get.toString else "-" + atom_map.get( atom ).get

  /**
   * Returns for a given clause and weight
   * a representation of it in .wcnf format
   *
   * @param clause clause to provide
   * @param weight weight of clause
   * @return a clause in .wcnf format
   */
  protected def getWCNFString( clause: HOLClause, weight: Int, atom_map: Map[HOLAtom, Int] ): String =
    {
      val sb = new StringBuilder()

      sb.append( weight + " " )
      def atoms_to_str( as: Seq[FOLAtom], pol: Boolean ) = as.foreach( a => {
        sb.append( getWCNFString( a, pol, atom_map ) );
        sb.append( " " );
      } )

      atoms_to_str( clause.positive.asInstanceOf[Seq[FOLAtom]], true )
      atoms_to_str( clause.negative.asInstanceOf[Seq[FOLAtom]], false )

      sb.toString()
    }

  def getWCNFInput(): StringBuilder = {
    val sb = new StringBuilder()
    val nl = System.getProperty( "line.separator" )
    var top = 1
    if ( soft.size == 0 ) {
      sb.append( "p wcnf " + atom_map.size + " " + clauses.size + nl )
    } else {
      top = soft.foldLeft( 0 )( ( acc, x ) => acc + x._2 ) + 1
      sb.append( "p wcnf " + atom_map.size + " " + clauses.size + " " + top + nl )
    }

    // construct qmaxsat text input
    hard.foreach( c =>
      {
        sb.append( getWCNFString( c, top, atom_map ) )
        sb.append( "0" )
        sb.append( nl )
      } )
    soft.foreach( c =>
      {
        sb.append( getWCNFString( c._1, c._2, atom_map ) )
        sb.append( "0" )
        sb.append( nl )
      } )
    sb
  }
}

object readWDIMACSOld {
  /**
   * A delegator to treat outputformats of different MaxSAT Solvers differently
   * @param in output of sepcific MaxSAT Solver
   * @param helper The helper object used for this input/output session.
   * @return None if UNSAT, Some(minimal model) otherwise
   */
  def apply( in: String, format: Format.Format, helper: WDIMACSHelper ): Option[Map[FOLFormula, Boolean]] =
    {
      format match {
        //case MaxSATSolver.QMaxSAT => {
        case Format.MultiVLine  => multiVLineOutputToInterpretation( in, helper )
        //}

        //case MaxSATSolver.ToySAT => {
        case Format.ToySAT      => toysatOutputToInterpretation( in, helper )
        //}
        //case MaxSATSolver.ToySolver => {
        //  multiVLineOutputToInterpretation( in )
        //}
        //case MaxSATSolver.MiniMaxSAT => {
        case Format.SingleVLine => singleVLineOutputToInterpretation( in, helper )
        //}
        case _                  => None
      }
    }
  /**
   * A method to treat outputformat of a MaxSATSolver with
   * a single line starting with a 'v'
   * @param in output string of the MaxSAT Solver
   * @return None if UNSAT, Some(minimal model) otherwise
   */
  private def singleVLineOutputToInterpretation( in: String, helper: DIMACSHelper ): Option[Map[FOLFormula, Boolean]] = {

    val oLinePattern = """(?m)^o.*""".r
    val vLinePattern = """(?m)^v.*""".r

    ( oLinePattern findFirstIn in ) match {
      case None => None
      case Some( str ) => {
        var weight = str.split( " " )( 1 ).toInt
        ( vLinePattern findFirstIn in ) match {
          case None => None
          case Some( vline ) => {
            Some( vline.split( " " ).
              filter( lit => !lit.equals( "" ) && !lit.equals( "v" ) && !lit.charAt( 0 ).equals( '0' ) ).
              map( lit =>
                if ( lit.charAt( 0 ) == '-' ) {
                  // negative literal
                  ( helper.getAtom( lit.substring( 1 ).toInt ).get.asInstanceOf[FOLFormula], false )
                } else {
                  // positive literal
                  ( helper.getAtom( lit.toInt ).get.asInstanceOf[FOLFormula], true )
                } ).toSet.toMap )
          }
        }
      }
    }
  }

  /**
   * A method to treat outputformat of a MaxSATSolver with
   * multiple lines starting with a 'v'
   * @param str output string of the MaxSAT Solver
   * @return None if UNSAT, Some(minimal model) otherwise
   */
  private def multiVLineOutputToInterpretation( str: String, helper: DIMACSHelper ): Option[Map[FOLFormula, Boolean]] = {
    val sLinePattern = """(?m)^s.*""".r
    val oLinePattern = """(?m)^o.*""".r
    val vLinePattern = """(?m)^v.*""".r

    val sat = ( sLinePattern findFirstIn str )
    if ( sat == None ) {
      return None
    } else {
      val satstrings = sat.get.split( " " )

      if ( satstrings.size > 1 && satstrings( 1 ) == "OPTIMUM" ) {
        val opt = ( oLinePattern findFirstIn str )
        var optstring = Array( "", "-1" )
        if ( opt != None ) {
          optstring = opt.get.split( " " )
        }

        var weight = optstring( 1 ).toInt
        // get all lines starting with v and drop the v
        val model = ( vLinePattern findAllIn str ).map( _.drop( 2 ).split( " " ) ).foldLeft( List[String]() )( ( v, acc ) => v ++ acc )
        return Some( model.
          filter( lit => !lit.equals( "" ) && !lit.equals( "v" ) && !lit.charAt( 0 ).equals( '0' ) ).
          map( lit =>
            if ( lit.charAt( 0 ) == '-' ) {
              // negative literal
              ( helper.getAtom( lit.substring( 1 ).toInt ).get.asInstanceOf[FOLFormula], false )
            } else {
              // positive literal
              ( helper.getAtom( lit.toInt ).get.asInstanceOf[FOLFormula], true )
            } )
          .toSet.toMap )
      }
    }
    return None
  }

  /**
   * A method to treat outputformat of the ToySAT
   * @param str output of ToySAT
   * @return None if UNSAT, Some(minimal model) otherwise
   */
  private def toysatOutputToInterpretation( str: String, helper: DIMACSHelper ): Option[Map[FOLFormula, Boolean]] = {
    val sLinePattern = """(?m)^s.*""".r
    val oLinePattern = """(?m)^o.*""".r
    val vLinePattern = """(?m)^v.*""".r

    val sat = ( sLinePattern findFirstIn str )
    if ( sat == None ) {
      return None
    } else {
      val satstrings = sat.get.split( " " )

      if ( satstrings.size > 1 && satstrings( 1 ) == "OPTIMUM" ) {
        val opt = ( oLinePattern findFirstIn str )
        var optstring = Array( "", "-1" )
        if ( opt != None ) {
          optstring = opt.get.split( " " )
        }

        var weight = optstring( 1 ).toInt
        // get all lines starting with v and drop the v
        val model = ( vLinePattern findAllIn str ).map( _.drop( 2 ).split( " " ) ).foldLeft( List[String]() )( ( v, acc ) => v ++ acc )
        return Some( model.
          filter( lit => !lit.equals( "" ) && !lit.equals( "v" ) && !lit.charAt( 0 ).equals( '0' ) ).
          map( lit =>
            if ( lit.charAt( 0 ) == '-' ) {
              // negative literal
              // HERE IS 1 of 2 DIFFERENCES TO TOYSOLVER
              ( helper.getAtom( lit.substring( 2 ).toInt ).get.asInstanceOf[FOLFormula], false )
            } else {
              // positive literal
              // HERE IS 1 of 2 DIFFERENCES TO TOYSOLVER
              ( helper.getAtom( lit.substring( 1 ).toInt ).get.asInstanceOf[FOLFormula], true )
            } )
          .toSet.toMap )
      }
    }
    return None
  }
}

/**
 * An enumeration to distinguish different output formats of
 * WCNF-based MaxSAT solvers.
 *
 */
object Format extends Enumeration {
  type Format = Value
  val MultiVLine, ToySAT, SingleVLine = Value
}
