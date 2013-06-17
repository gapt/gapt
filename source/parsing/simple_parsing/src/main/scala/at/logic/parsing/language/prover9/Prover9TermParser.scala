package at.logic.parsing.language.prover9

import util.parsing.combinator.JavaTokenParsers
import at.logic.language.fol
import fol._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.lk.base.types.FSequent
import at.logic.language.hol.HOLFormula
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.types.Ti
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.types.Ti
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import scala.collection.immutable
import scala.util.parsing.combinator.PackratParsers

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
  override def varsymb: Parser[String] =  """[A-Z][a-zA-Z0-9_]*""".r

}

//LADR Style Term Parser
object Prover9TermParserLadrStyle extends Prover9TermParserA {
  override def conssymb: Parser[String] = """([a-tA-Z][a-zA-Z0-9_]*)|([0-9]+)""".r
  override def varsymb: Parser[String] =  """[u-z][a-zA-Z0-9_]*""".r

}


abstract trait Prover9TermParserA extends JavaTokenParsers with PackratParsers {
  /* these two rules are abstract since the variable style decides the regexp for a variable */
  def conssymb : Parser[String]
  def varsymb : Parser[String]

  /* change this variable to to use prolog style variables (starting with upper case letters) or ladr style variables
  *  (starting with u-z)*/

  /* debug transformers
  def d(s:String,f:FOLFormula) : FOLFormula = { println(s+": "+f); f }    */

  /* The main entry point to the parser for prover9 formulas. To parse literals, use literal as the entry point. */
  def parseFormula(s:String) : FOLFormula = parseAll(formula, s) match {
    case Success(result, _) => result
    case NoSuccess(msg, input) =>
      throw new Exception("Error parsing prover9 formula '"+s+"' at position "+input.pos+". Error message: "+msg)
  }

  lazy val pformula : PackratParser[FOLFormula] = parens(formula) | allformula | exformula
  lazy val formula: PackratParser[FOLFormula] = implication
  //precedence 800
  lazy val implication: PackratParser[FOLFormula]  = (dis_or_con ~ ("<->"|"->"|"<-") ~ dis_or_con) ^^ { _ match {
    case f ~ "->"  ~ g => fol.Imp(f,g)
    case f ~ "<-"  ~ g => fol.Imp(g,f)
    case f ~ "<->" ~ g => fol.And(fol.Imp(f,g), fol.Imp(g,f))
  }} | dis_or_con

  lazy val dis_or_con: PackratParser[FOLFormula] = (disjunction | conlit )
  //precedence 790
  lazy val disjunction: PackratParser[FOLFormula]  = (conlit ~ ("|" ~> disjunction) ^^ {case f ~ g => fol.Or(f,g)}) | conlit
  //precedence 780
  lazy val conlit: PackratParser[FOLFormula] =  (conjunction| qliteral )
  lazy val conjunction: PackratParser[FOLFormula]  = ( qliteral ~ ("&" ~> conjunction)   ^^ { case f ~ g => fol.And(f,g) }) | qliteral
  //precedence 750
  lazy val qliteral : PackratParser[FOLFormula] = allformula | exformula | literal2
  lazy val allformula : PackratParser[FOLFormula] = parens(allformula_)
  lazy val exformula : PackratParser[FOLFormula] = parens(exformula_)
  lazy val allformula_ : PackratParser[FOLFormula]   = ("all"    ~> variable ~ ( allformula_ | exformula_ | literal2) ) ^^ { case v ~ f => fol.AllVar(v,f) }
  lazy val exformula_ : PackratParser[FOLFormula]    = ("exists" ~> variable ~ ( allformula_ | exformula_ | literal2) ) ^^ { case v ~ f => fol.ExVar(v,f) }

  //precedence 300
  lazy val literal2:PackratParser[FOLFormula] = pformula | atomWeq | negation
  lazy val negation:PackratParser[FOLFormula] = "-" ~> (pformula | negation |atomWeq) ^^ { x => fol.Neg(x) }


  def parens[T](p:Parser[T]) : Parser[T] = "(" ~> p <~ ")"

  lazy val literal: PackratParser[FOLFormula] = iatom | negatom | posatom
  lazy val posatom: PackratParser[FOLFormula] = atom
  lazy val negatom: PackratParser[FOLFormula] = "-" ~ atom  ^^ {case "-" ~ a => Neg(a)}
  lazy val atomWeq: PackratParser[FOLFormula] =  iatom | atom
  lazy val atom: PackratParser[FOLFormula] = atom1 | atom2 | topbottom
  lazy val atom1: PackratParser[FOLFormula] = atomsymb ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Atom(ConstantStringSymbol(x), params.asInstanceOf[List[FOLTerm]])}
  lazy val atom2: PackratParser[FOLFormula] = atomsymb ^^ {case x => Atom(ConstantStringSymbol(x), Nil)}

  val plus_sym = ConstantStringSymbol("+")
  val times_sym = ConstantStringSymbol("*")
  val minus_sym = ConstantStringSymbol("-")
  val div_sym = ConstantStringSymbol("-")
  val wedge_sym = ConstantStringSymbol("^")
//  val vee_sym = ConstantStringSymbol("v")
  val less_sym = ConstantStringSymbol("<")
  val greater_sym = ConstantStringSymbol(">")
  val lesseq_sym = ConstantStringSymbol("<=")
  val greatereq_sym = ConstantStringSymbol(">=")

  //infixatom
  lazy val iatom : PackratParser[FOLFormula] = term ~ """((<|>)=?)|(!?=)|[+\-*]""".r  ~ term ^^ {
    _ match {
      case t1 ~ "=" ~ t2 => Equation(t1,t2)
      case t1 ~ "!=" ~ t2 => Neg(Equation(t1,t2))
      case t1 ~ "<" ~ t2 => Atom(less_sym, List(t1,t2))
      case t1 ~ ">" ~ t2 => Atom(greater_sym, List(t1,t2))
      case t1 ~ "<=" ~ t2 => Atom(lesseq_sym, List(t1,t2))
      case t1 ~ ">=" ~ t2 => Atom(greatereq_sym, List(t1,t2))
      case t1 ~ sym ~ t2 => fol.Atom(ConstantStringSymbol(sym), List(t1,t2))
    }
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
  lazy val ifunction: PackratParser[FOLTerm] = (noniterm|parens(ifunction)) ~ """[+\-*/^]""".r ~ (noniterm|parens(ifunction)) ^^ {
    _ match {
      case t1 ~ "+" ~ t2 => fol.Function(plus_sym, List(t1,t2))
      case t1 ~ "-" ~ t2 => fol.Function(minus_sym, List(t1,t2))
      case t1 ~ "*" ~ t2 => fol.Function(times_sym, List(t1,t2))
      case t1 ~ "/" ~ t2 => fol.Function(div_sym, List(t1,t2))
      case t1 ~ "^" ~ t2 => fol.Function(wedge_sym, List(t1,t2))
      case t1 ~ sym ~ t2 => fol.Function(ConstantStringSymbol(sym), List(t1,t2))
    }
  }
  lazy val function: PackratParser[FOLTerm] = conssymb ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Function(ConstantStringSymbol(x), params.asInstanceOf[List[FOLTerm]])}
  lazy val constant: PackratParser[FOLConst] = conssymb ^^ {case x => FOLFactory.createVar(ConstantStringSymbol(x), Ti()).asInstanceOf[FOLConst]}
  lazy val variable: PackratParser[FOLVar] = varsymb ^^ {case x => FOLFactory.createVar(VariableStringSymbol(x), Ti()).asInstanceOf[FOLVar]}
  lazy val topbottom: PackratParser[FOLFormula] = "$" ~> ( "T" ^^ (x=> topformula) | "F" ^^ (x => bottomformula) )

  //we don't have top and bottom in the algorithms, so we simulate it
  val topformula = { fol.And( fol.TopC, fol.Neg(fol.TopC)  ) }
  val bottomformula = { fol.Or( fol.BottomC, fol.Neg(fol.BottomC)  ) }


  def createNOp(fs:List[FOLFormula], constructor : (FOLFormula, FOLFormula) => FOLFormula ) : FOLFormula = {
    //if (fs.size < 2) failure("Binary operator needs to occur at least once!") else
    fs.reduceRight( (f:FOLFormula, g:FOLFormula) => constructor(f,g)   )
  }

  def normalizeFSequent(f:FSequent) = {
    require( (f.antecedent ++ f.succedent).forall(_.isInstanceOf[FOLFormula]), "normalization only works on FOL formulas" )
    FSequent(f.antecedent.map(x => normalizeFormula(x.asInstanceOf[FOLFormula])),
      f.succedent.map(x => normalizeFormula(x.asInstanceOf[FOLFormula])))
  }

  def normalizeFormula(f:FOLFormula) : HOLFormula = {
    val freevars = f.freeVariables.toList
    val pairs : List[(Var,FOLExpression)] = (freevars zip (0 to (freevars.size-1))) map (x => (x._1,  x._1.factory.createVar(VariableStringSymbol("v"+x._2), x._1.exptype).asInstanceOf[FOLExpression]) )
    val nf : FOLFormula = Substitution(pairs)(f).asInstanceOf[FOLFormula]

    //TODO: create blacklist
    Normalization(nf,freevars.size, "v", immutable.HashSet[String]())._1
  }


}

