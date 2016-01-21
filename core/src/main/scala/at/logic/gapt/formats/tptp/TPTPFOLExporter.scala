/*
 * TPTPFOLParser.scala
 *
 */

package at.logic.gapt.formats.tptp

import at.logic.gapt.expr.fol.{ reduceHolToFol }
import at.logic.gapt.proofs.HOLSequent
import scala.collection.immutable.HashMap
import at.logic.gapt.expr._
import scala.collection.mutable

object TPTPFOLExporter extends at.logic.gapt.utils.logging.Logger {
  val nLine = sys.props( "line.separator" )

  // convert a named list of clauses to a CNF refutation problem.
  // TODO: have to give a different name because of erasure :-(
  def tptp_problem_named( ss: List[Tuple2[String, HOLSequent]] ) =
    ss.foldLeft( "" )( ( s, p ) => s + sequentToProblem( p._2, p._1 ) + nLine )

  // Convert a sequent into a tptp proof problem.
  def tptp_proof_problem( seq: HOLSequent ) =
    "fof( to_prove, conjecture, " + exportFormula( seq.toFormula.asInstanceOf[FOLFormula] ) + ")." + nLine

  def tptp_proof_problem_split( seq: HOLSequent ) =
    ( seq.antecedent.map( _ -> "axiom" ) ++ seq.succedent.map( _ -> "conjecture" ) ).zipWithIndex.map {
      case ( ( formula: FOLFormula, role ), index ) =>
        s"fof( formula$index, $role, ${exportFormula( formula )} )." + nLine
    }.mkString

  // convert a list of clauses to a CNF refutation problem.
  def tptp_problem( ss: List[HOLSequent] ) =
    tptp_problem_named( ss.zipWithIndex.map( p => ( "sequent" + p._2, p._1 ) ) )

  def sequentToProblemFull( s: HOLSequent, n: String ) =
    "fof( " + n + ",axiom," + export( s ) + ")."

  def sequentToProblem( s: HOLSequent, n: String ) =
    "cnf( " + n + ",axiom," + export( s ) + ")."

  // TODO: would like to have FOLSequent here --- instead, we cast
  // we export it as a disjunction
  def export( s: HOLSequent ) = {
    val f = reduceHolToFol( s.toFormula )
    val map = getVarRenaming( f )
    trace( "var renaming: " + map )
    tptp( f )( map )
  }

  def exportFormula( f: FOLFormula ) = {
    val map = getVarRenaming( f )
    trace( "var renaming for " + f + ": " + map )
    tptpFormula( f )( map )
  }

  def getVarRenaming( f: FOLFormula ) = {
    freeVariables( f ).toList.zipWithIndex.foldLeft( new HashMap[FOLVar, String] )( ( m, p ) =>
      m + ( p._1 -> ( "X" + p._2.toString ) ) )
  }

  def tptp( e: FOLExpression )( implicit s_map: Map[FOLVar, String] ): String = e match {
    case f: FOLFormula => tptp( f )
    case t: FOLTerm    => tptp( t )
  }

  // To be able to deal with theorem provers that implement only
  // the parsing of clauses (i.e. they assume associativity of |
  // and dislike parentheses), we only export clauses at the moment.
  def tptp( f: FOLFormula )( implicit s_map: Map[FOLVar, String] ): String = f match {
    case Top()              => "$true"
    case Bottom()           => "$false"
    case FOLAtom( x, args ) => handleAtom( x, args )
    case Or( x, y )         => tptp( x ) + " | " + tptp( y )
    case Neg( x )           => "~" + tptp( x )
  }

  private def addToMap( v: FOLVar )( implicit s_map: Map[FOLVar, String] ) = {
    s_map + ( ( v, "X" + s_map.size ) )
  }

  // Exports a full formula in TPTP format.
  def tptpFormula( f: FOLFormula )( implicit s_map: Map[FOLVar, String] ): String = f match {
    case Top()              => "$true"
    case Bottom()           => "$false"
    case FOLAtom( x, args ) => handleAtom( x, args )
    case Or( x, y )         => "( " + tptpFormula( x ) + " | " + tptpFormula( y ) + " )"
    case Neg( x )           => "( ~" + tptpFormula( x ) + ")"
    case And( x, y )        => "( " + tptpFormula( x ) + " & " + tptpFormula( y ) + " )"
    case Imp( x, y )        => "( " + tptpFormula( x ) + " => " + tptpFormula( y ) + " )"
    case All( v, f ) => {
      val new_map = addToMap( v )
      "(! [" + tptp( v )( new_map ) + "] : " + tptpFormula( f )( new_map ) + ")"
    }
    case Ex( v, f ) =>
      {
        val new_map = addToMap( v )
        "(? [" + tptp( v )( new_map ) + "] : " + tptpFormula( f )( new_map ) + ")"
      }
  }

  def tptp( t: FOLTerm )( implicit s_map: Map[FOLVar, String] ): String = t match {
    case FOLConst( c )          => single_quote( c.toString )
    case x: FOLVar              => s_map( x )
    case FOLFunction( x, args ) => handleAtom( x, args )
  }

  def handleAtom( x: String, args: List[FOLTerm] )( implicit s_map: Map[FOLVar, String] ) =
    if ( x.toString.equals( "=" ) )
      tptp( args.head ) + " = " + tptp( args.last )
    else
      single_quote( x.toString ) + (
        if ( args.size == 0 )
          ""
        else
          "(" + tptp( args.head ) +
            args.tail.foldLeft( "" )( ( s, a ) => s + ", " + tptp( a ) )
            + ")"
      )

  def single_quote( s: String ) = "'" + s + "'"
}
