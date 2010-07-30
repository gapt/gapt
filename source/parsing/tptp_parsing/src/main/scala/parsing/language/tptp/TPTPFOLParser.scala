/*
 * TPTPFOLParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.language.tptp

import at.logic.language.hol.{HOLVar,HOLConst, HOLExpression, HOLFormula}
import at.logic.language.fol._
import at.logic.language.lambda.types._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.calculi.lk.base.Sequent
import scala.collection.immutable.{HashSet, HashMap}
import at.logic.language.fol._
import at.logic.algorithms.fol.hol2fol._

object TPTPFOLExporter {
  // FIXME: this should not be here!
  def hol2fol(f: HOLFormula) = 
  {
    val imap = scala.collection.mutable.Map[at.logic.language.lambda.typedLambdaCalculus.LambdaExpression, at.logic.language.hol.logicSymbols.ConstantStringSymbol]()
    val iid = new {var idd = 0; def nextId = {idd = idd+1; idd}}
    reduceHolToFol(f, imap, iid )
  }

  def tptp_problem( ss: List[Sequent] ) = 
    ss.zipWithIndex.foldLeft("")( (s, p) => s + sequentToProblem( p._1, "sequent" + p._2 ) + "\n")

  def sequentToProblem( s: Sequent, n: String ) =
    "cnf( " + n + ",axiom," + export( s ) + ")."

  // TODO: would like to have FOLSequent here --- instead, we convert
  // we export it as a disjunction
  def export( s: Sequent ) = {
    val f = hol2fol(s.toFormula).asInstanceOf[FOLFormula]
    val map = getFreeVarRenaming( f )
    tptp( f )( map )
  }

  def getFreeVarRenaming( f: FOLFormula ) = {
    getFreeVariablesFOL( f ).toList.zipWithIndex.foldLeft( new HashMap[FOLVar, String] )( (m, p) =>
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

  def tptp( t: FOLTerm )(implicit s_map: Map[FOLVar, String]) : String = t match {
    case FOLConst(c) => single_quote( c.toString )
    case FOLVar(x) => s_map( t.asInstanceOf[FOLVar] )
    case Function(x, args) => handleAtom( x, args )
  }

  def handleAtom( x: ConstantSymbolA, args: List[FOLTerm] )(implicit s_map: Map[FOLVar, String]) =
    single_quote( x.toString ) + (
    if (args.size == 0)
      ""
    else
      "(" + tptp( args.head ) + 
      args.tail.foldLeft("")((s,a) => s + ", " + tptp( a ) )
      + ")" )

  def single_quote( s: String ) = "'" + s + "'"
}
