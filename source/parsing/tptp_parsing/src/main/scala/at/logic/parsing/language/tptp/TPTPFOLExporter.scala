/*
 * TPTPFOLParser.scala
 *
 */

package at.logic.parsing.language.tptp

import at.logic.algorithms.fol.hol2fol._
import at.logic.language.fol._
import at.logic.language.lambda.symbols.{StringSymbol, SymbolA}
import at.logic.calculi.lk.base.FSequent
import scala.collection.immutable.HashMap
import at.logic.language.hol.HOLFormula
import at.logic.language.hol
import scala.collection.mutable
import at.logic.language.lambda.LambdaExpression

object TPTPFOLExporter extends at.logic.utils.logging.Logger {
  // FIXME: this should not be here!
  def hol2fol(f: HOLFormula) : FOLFormula = 
  {
    val imap = mutable.Map[LambdaExpression, StringSymbol]()
    val iid = new {var idd = 0; def nextId = {idd = idd+1; idd}}
    convertHolToFol(f)
  } 

  // convert a named list of clauses to a CNF refutation problem.
  // TODO: have to give a different name because of erasure :-(
  def tptp_problem_named( ss: List[Tuple2[String, FSequent]] ) =
    ss.foldLeft("")( (s, p) => s + sequentToProblem( p._2, p._1 ) + "\n")

  // Convert a sequent into a tptp proof problem.
  def tptp_proof_problem( seq : FSequent ) =
    "fof( to_prove, conjecture, " + exportFormula ( hol2fol( seq.toFormula ) )+ ").\n"

  // convert a list of clauses to a CNF refutation problem.
  def tptp_problem( ss: List[FSequent] ) =
    tptp_problem_named( ss.zipWithIndex.map( p => ( "sequent" + p._2, p._1 ) ) )

  def sequentToProblemFull( s: FSequent, n: String ) =
    "fof( " + n + ",axiom," + export( s ) + ")."

  def sequentToProblem( s: FSequent, n: String ) =
    "cnf( " + n + ",axiom," + export( s ) + ")."

  // TODO: would like to have FOLSequent here --- instead, we cast
  // we export it as a disjunction
  def export( s: FSequent ) = {
    val f = reduceHolToFol(s.toFormula)
    val map = getVarRenaming( f )
    trace("var renaming: " + map)
    tptp( f )( map )
  }

  def exportFormula( f: FOLFormula ) = {
    val map = getVarRenaming( f )
    trace("var renaming for " + f + ": " + map)
    tptpFormula( f )( map )
  }

  def getVarRenaming( f: FOLFormula ) = {
    freeVariables( f ).toList.zipWithIndex.foldLeft( new HashMap[FOLVar, String] )( (m, p) =>
      m + (p._1 -> ("X" + p._2.toString) )
    )
  }

  def tptp( e: FOLExpression )(implicit s_map: Map[FOLVar, String]) : String = e match {
    case f: FOLFormula => tptp( f )
    case t: FOLTerm => tptp( t )
  }

  // To be able to deal with theorem provers that implement only
  // the parsing of clauses (i.e. they assume associativity of |
  // and dislike parentheses), we only export clauses at the moment.
  def tptp( f: FOLFormula )(implicit s_map: Map[FOLVar, String]) : String = f match {
    case Atom(x, args) => handleAtom( x, args )
    case Or(x,y) => tptp( x ) + " | " + tptp( y )
    case Neg(x) => "~" + tptp( x )
  }

  private def addToMap( v : FOLVar )(implicit s_map: Map[FOLVar, String]) = {
    s_map + ((v, "X" + s_map.size))
  }
  
  // Exports a full formula in TPTP format.
  def tptpFormula( f : FOLFormula ) (implicit s_map: Map[FOLVar, String]) : String = f match {
    case Atom(x, args) => handleAtom( x, args )
    case Or(x,y) => "( " + tptpFormula( x ) + " | " + tptpFormula( y ) + " )"
    case Neg(x) => "( ~" + tptpFormula( x ) + ")"
    case And(x,y) => "( " + tptpFormula( x ) + " & " + tptpFormula( y ) + " )"
    case Imp(x,y) => "( " + tptpFormula( x ) + " => " + tptpFormula( y ) + " )"
    case AllVar(v, f) => {
      val new_map = addToMap(v)
      "(! [" + tptp(v)(new_map) + "] : " + tptpFormula(f)(new_map) + ")"
    }
    case ExVar(v, f) => 
    {
      val new_map = addToMap(v)
      "(? [" + tptp(v)(new_map) + "] : " + tptpFormula(f)(new_map) + ")"
    }
  }

  def tptp( t: FOLTerm )(implicit s_map: Map[FOLVar, String]) : String = t match {
    case FOLConst(c) => single_quote( c.toString )
    case x : FOLVar => s_map( x ) 
    case Function(x, args) => handleAtom( x, args )
  }

  def handleAtom( x: SymbolA, args: List[FOLTerm] )(implicit s_map: Map[FOLVar, String]) =
    if ( x.toString.equals("=") )
      tptp( args.head ) + " = " + tptp( args.last )
    else
      single_quote( x.toString ) + (
      if (args.size == 0)
        ""
      else
        "(" + tptp( args.head ) + 
        args.tail.foldLeft("")((s,a) => s + ", " + tptp( a ) )
        + ")" )

  def single_quote( s: String ) = "'" + s + "'"
}

object TPTPfofExporter {
  def apply(conjectures: Seq[FOLFormula]) = generate_file(Nil, conjectures)
  def apply(axioms : Seq[FOLFormula], conjectures: Seq[FOLFormula]) = generate_file(axioms, conjectures)

  def generate_file(axioms : Seq[FOLFormula], conjectures : Seq[FOLFormula]) = {
    val builder = new StringBuilder()

    var count = 0
    for (formula <- axioms) {
      builder append ("fof(axiom")
      builder append (count)
      builder append (", axiom, ")
      //builder append (Renaming.fol_as_tptp(formula) )
      builder append (").\n\n")

      count = count + 1
    }

    for (formula <- conjectures) {
      builder append ("fof(formula")
      builder append (count)
      builder append (", conjecture, ")
      //builder append (Renaming.fol_as_tptp(formula) )
      builder append (").\n\n")

      count = count + 1
    }
    builder.toString()
  }

}

