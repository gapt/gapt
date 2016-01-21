package at.logic.gapt.formats.prover9

import at.logic.gapt.proofs.HOLSequent

import util.parsing.combinator.JavaTokenParsers
import at.logic.gapt.expr._
import scala.util.parsing.combinator.PackratParsers
import scala.collection.immutable.HashSet

/**
 * Parser for first order formulas in the prover 9 format.
 * ( http://www.cs.unm.edu/~mccune/mace4/manual/2009-11A/syntax.html )
 * Right associative, infix operators: &, |, all, exists
 * Infix operators: =, !=, <, >, , <=, >=, ->, <-, <->
 * Operator precedence (higher up in the list means binds weaker i.e. operator is closer to the root):
 *    ->, <-, <->
 *    all, exists
 *    =, !=, <, >, , <=, >=
 *    -
 * Operators missing: +,*,@,/,\, /\, \/,'
 * Unhandled cases prover9 accepts (extended as exceptions are encountered):
 *    (all 1 P(1))
 *
 */

//Prolog Style Term Parser
object Prover9TermParser extends Prover9TermParserA {
  override def conssymb: Parser[String] = """([a-z][a-zA-Z0-9_]*)|([0-9]+)""".r
  override def varsymb: Parser[String] = """[A-Z][a-zA-Z0-9_]*""".r

}

//LADR Style Term Parser
object Prover9TermParserLadrStyle extends Prover9TermParserA {
  override def conssymb: Parser[String] = """([a-tA-Z][a-zA-Z0-9_]*)|([0-9]+)""".r
  override def varsymb: Parser[String] = """[u-z][a-zA-Z0-9_]*""".r

}

abstract trait Prover9TermParserA extends JavaTokenParsers with PackratParsers {
  /* these two rules are abstract since the variable style decides the regexp for a variable */
  def conssymb: Parser[String]
  def varsymb: Parser[String]

  /* change this variable to to use prolog style variables (starting with upper case letters) or ladr style variables
  *  (starting with u-z)*/

  /* debug transformers
  def d(s:String,f:FOLFormula) : FOLFormula = { println(s+": "+f); f }    */

  /* The main entry point to the parser for prover9 formulas. To parse literals, use literal as the entry point. */
  def parseFormula( s: String ): FOLFormula = parseAll( formula, s ) match {
    case Success( result, _ ) => result
    case NoSuccess( msg, input ) =>
      throw new Exception( "Error parsing prover9 formula '" + s + "' at position " + input.pos + ". Error message: " + msg )
  }

  def parseTerm( s: String ): FOLTerm = parseAll( term, s ) match {
    case Success( result, _ ) => result
    case NoSuccess( msg, input ) =>
      throw new Exception( "Error parsing prover9 term '" + s + "' at position " + input.pos + ". Error message: " + msg )
  }

  lazy val pformula: PackratParser[FOLFormula] = parens( formula ) | allformula | exformula
  lazy val formula: PackratParser[FOLFormula] = implication
  //precedence 800
  lazy val implication: PackratParser[FOLFormula] = ( dis_or_con ~ ( "<->" | "->" | "<-" ) ~ dis_or_con ) ^^ {
    _ match {
      case f ~ "->" ~ g  => Imp( f, g )
      case f ~ "<-" ~ g  => Imp( g, f )
      case f ~ "<->" ~ g => And( Imp( f, g ), Imp( g, f ) )
    }
  } | dis_or_con

  lazy val dis_or_con: PackratParser[FOLFormula] = ( disjunction | conlit )
  //precedence 790
  lazy val disjunction: PackratParser[FOLFormula] = ( conlit ~ ( "|" ~> disjunction ) ^^ { case f ~ g => Or( f, g ) } ) | conlit
  //precedence 780
  lazy val conlit: PackratParser[FOLFormula] = ( conjunction | qliteral )
  lazy val conjunction: PackratParser[FOLFormula] = ( qliteral ~ ( "&" ~> conjunction ) ^^ { case f ~ g => And( f, g ) } ) | qliteral
  //precedence 750
  lazy val qliteral: PackratParser[FOLFormula] = allformula | exformula | literal2
  lazy val allformula: PackratParser[FOLFormula] = parens( allformula_ )
  lazy val exformula: PackratParser[FOLFormula] = parens( exformula_ )
  lazy val allformula_ : PackratParser[FOLFormula] = ( "all" ~> variable ~ ( allformula_ | exformula_ | literal2 ) ) ^^ { case v ~ f => All( v, f ) }
  lazy val exformula_ : PackratParser[FOLFormula] = ( "exists" ~> variable ~ ( allformula_ | exformula_ | literal2 ) ) ^^ { case v ~ f => Ex( v, f ) }

  //precedence 300
  lazy val literal2: PackratParser[FOLFormula] = pformula | atomWeq | negation
  lazy val negation: PackratParser[FOLFormula] = "-" ~> ( pformula | negation | atomWeq ) ^^ { x => Neg( x ) }

  def parens[T]( p: Parser[T] ): Parser[T] = "(" ~> p <~ ")"

  lazy val literal: PackratParser[FOLFormula] = iatom | negatom | posatom
  lazy val posatom: PackratParser[FOLFormula] = atom
  lazy val negatom: PackratParser[FOLFormula] = "-" ~ atom ^^ { case "-" ~ a => Neg( a ) }
  lazy val atomWeq: PackratParser[FOLFormula] = iatom | atom
  lazy val atom: PackratParser[FOLFormula] = atom1 | atom2 | topbottom
  lazy val atom1: PackratParser[FOLFormula] = atomsymb ~ "(" ~ repsep( term, "," ) ~ ")" ^^ {
    case x ~ "(" ~ params ~ ")" => FOLAtom( x, params.asInstanceOf[List[FOLTerm]] )
  }
  lazy val atom2: PackratParser[FOLFormula] = atomsymb ^^ { case x => FOLAtom( x, Nil ) }

  val plus_sym = "+"
  val times_sym = "*"
  val minus_sym = "-"
  val div_sym = "-"
  val wedge_sym = "^"
  //  val vee_sym = ("v")
  val less_sym = "<"
  val greater_sym = ">"
  val lesseq_sym = "<="
  val greatereq_sym = ">="

  //infixatom
  lazy val iatom: PackratParser[FOLFormula] = term ~ """((<|>)=?)|(!?=)|[+\-*]""".r ~ term ^^ {
    case t1 ~ "=" ~ t2  => Eq( t1, t2 )
    case t1 ~ "!=" ~ t2 => Neg( Eq( t1, t2 ) )
    case t1 ~ "<" ~ t2  => FOLAtom( less_sym, List( t1, t2 ) )
    case t1 ~ ">" ~ t2  => FOLAtom( greater_sym, List( t1, t2 ) )
    case t1 ~ "<=" ~ t2 => FOLAtom( lesseq_sym, List( t1, t2 ) )
    case t1 ~ ">=" ~ t2 => FOLAtom( greatereq_sym, List( t1, t2 ) )
    case t1 ~ sym ~ t2  => FOLAtom( sym, List( t1, t2 ) )
  }
  /*
  def iatom: Parser[FOLFormula] = poseq | negeq
  def poseq: Parser[FOLFormula] = term ~ "=" ~ term ^^ {case t1 ~ "=" ~ t2 => Equation(t1,t2)}
  def negeq: Parser[FOLFormula] = term ~ "!=" ~ term ^^ {case t1 ~ "!=" ~ t2 => Neg(Equation(t1,t2))}
  def orderings : Parser[FOLFormula] = term ~ """(<|>)=?""".r  ~ term ^^ { case t1 ~ sym ~ t2 => fol.Atom(ConstantStringSymbol(sym), List(t1,t2))}
  */
  lazy val atomsymb: Parser[String] = """[a-zA-Z][a-zA-Z0-9_]*""".r
  lazy val term: PackratParser[FOLTerm] = ifunction | noniterm
  lazy val noniterm: PackratParser[FOLTerm] = function | constant | variable
  lazy val ifunction: PackratParser[FOLTerm] = ( noniterm | parens( ifunction ) ) ~ """[+\-*/^v]""".r ~ ( noniterm | parens( ifunction ) ) ^^ {
    case t1 ~ "+" ~ t2 => FOLFunction( plus_sym, List( t1, t2 ) )
    case t1 ~ "-" ~ t2 => FOLFunction( minus_sym, List( t1, t2 ) )
    case t1 ~ "*" ~ t2 => FOLFunction( times_sym, List( t1, t2 ) )
    case t1 ~ "/" ~ t2 => FOLFunction( div_sym, List( t1, t2 ) )
    case t1 ~ "^" ~ t2 => FOLFunction( wedge_sym, List( t1, t2 ) )
    case t1 ~ sym ~ t2 => FOLFunction( sym, List( t1, t2 ) )
  }
  lazy val function: PackratParser[FOLTerm] = conssymb ~ "(" ~ repsep( term, "," ) ~ ")" ^^ {
    case x ~ "(" ~ params ~ ")" => FOLFunction( x, params.asInstanceOf[List[FOLTerm]] )
  }
  lazy val constant: PackratParser[FOLTerm] = conssymb ^^ {
    case x => FOLConst( x )
  }
  lazy val variable: PackratParser[FOLVar] = varsymb ^^ { FOLVar( _ ) }
  lazy val topbottom: PackratParser[FOLFormula] = "$" ~> ( "T" ^^ ( x => Top() ) | "F" ^^ ( x => Bottom() ) )

  def createNOp( fs: List[FOLFormula], constructor: ( FOLFormula, FOLFormula ) => FOLFormula ): FOLFormula = {
    //if (fs.size < 2) failure("Binary operator needs to occur at least once!") else
    fs.reduceRight( ( f: FOLFormula, g: FOLFormula ) => constructor( f, g ) )
  }

  def normalizeFSequent( f: HOLSequent ) = {
    require( ( f.antecedent ++ f.succedent ).forall( _.isInstanceOf[FOLFormula] ), "normalization only works on FOL formulas" )
    HOLSequent(
      f.antecedent.map( x => normalizeFormula( x.asInstanceOf[FOLFormula] ) ),
      f.succedent.map( x => normalizeFormula( x.asInstanceOf[FOLFormula] ) )
    )
  }

  def normalizeFormula( f: FOLFormula ): FOLFormula = {
    val freevars: List[( FOLVar, Int )] = freeVariables( f ).toList.zipWithIndex
    val pairs: List[( FOLVar, FOLVar )] = freevars.map( x => { ( x._1, FOLVar( "v" + x._2 ) ) } )
    val nf: FOLFormula = FOLSubstitution( pairs )( f )
    nf
  }

}

