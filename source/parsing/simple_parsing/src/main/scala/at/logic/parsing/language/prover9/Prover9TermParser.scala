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
import at.logic.language.lambda.typedLambdaCalculus.{Abs, App, LambdaExpression, Var}
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.types.Ti
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.substitutions.Substitution

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
 * Unhandled cases prover9 accepts (extended as exceptions are ancountered):
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


abstract class Prover9TermParserA extends JavaTokenParsers {
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

  def pformula : Parser[FOLFormula] = parens(formula) | allformula | exformula
  def formula: Parser[FOLFormula] = implication
  //precedence 800
  def implication: Parser[FOLFormula]  = (dis_or_con ~ ("<->"|"->"|"<-") ~ dis_or_con) ^^ { _ match {
    case f ~ "->"  ~ g => fol.Imp(f,g)
    case f ~ "<-"  ~ g => fol.Imp(g,f)
    case f ~ "<->" ~ g => fol.And(fol.Imp(f,g), fol.Imp(g,f))
  }} | dis_or_con

  def dis_or_con: Parser[FOLFormula] = (disjunction | conlit )
  //precedence 790
  def disjunction: Parser[FOLFormula]  = (conlit ~ ("|" ~> disjunction) ^^ {case f ~ g => fol.Or(f,g)}) | conlit
  //precedence 780
  def conlit: Parser[FOLFormula] =  (conjunction| qliteral )
  def conjunction: Parser[FOLFormula]  = ( qliteral ~ ("&" ~> conjunction)   ^^ { case f ~ g => fol.And(f,g) }) | qliteral
  //precedence 750
  def qliteral : Parser[FOLFormula] = allformula | exformula | literal2
  def allformula : Parser[FOLFormula] = parens(allformula_)
  def exformula : Parser[FOLFormula] = parens(exformula_)
  def allformula_ : Parser[FOLFormula]   = ("all"    ~> variable ~ ( allformula_ | exformula_ | literal2) ) ^^ { case v ~ f => fol.AllVar(v,f) }
  def exformula_ : Parser[FOLFormula]    = ("exists" ~> variable ~ ( allformula_ | exformula_ | literal2) ) ^^ { case v ~ f => fol.ExVar(v,f) }

  //precedence 300
  def literal2:Parser[FOLFormula] = pformula | atomWeq | negation
  def negation:Parser[FOLFormula] = "-" ~> (pformula | negation |atomWeq) ^^ { x => fol.Neg(x) }


  def parens[T](p:Parser[T]) : Parser[T] = "(" ~> p <~ ")"

  def literal: Parser[FOLFormula] = iatom | negatom | posatom
  def posatom: Parser[FOLFormula] = atom
  def negatom: Parser[FOLFormula] = "-" ~ atom  ^^ {case "-" ~ a => Neg(a)}
  def atomWeq: Parser[FOLFormula] =  iatom | atom
  def atom: Parser[FOLFormula] = atom1 | atom2 | topbottom
  def atom1: Parser[FOLFormula] = atomsymb ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Atom(ConstantStringSymbol(x), params.asInstanceOf[List[FOLTerm]])}
  def atom2: Parser[FOLFormula] = atomsymb ^^ {case x => Atom(ConstantStringSymbol(x), Nil)}

  //infixatom
  def iatom : Parser[FOLFormula] = term ~ """((<|>)=?)|(!?=)""".r  ~ term ^^ {
    _ match {
      case t1 ~ "=" ~ t2 => Equation(t1,t2)
      case t1 ~ "!=" ~ t2 => Neg(Equation(t1,t2))
      case t1 ~ sym ~ t2 => fol.Atom(ConstantStringSymbol(sym), List(t1,t2))
    }
  }
  /*
  def iatom: Parser[FOLFormula] = poseq | negeq
  def poseq: Parser[FOLFormula] = term ~ "=" ~ term ^^ {case t1 ~ "=" ~ t2 => Equation(t1,t2)}
  def negeq: Parser[FOLFormula] = term ~ "!=" ~ term ^^ {case t1 ~ "!=" ~ t2 => Neg(Equation(t1,t2))}
  def orderings : Parser[FOLFormula] = term ~ """(<|>)=?""".r  ~ term ^^ { case t1 ~ sym ~ t2 => fol.Atom(ConstantStringSymbol(sym), List(t1,t2))}
  */
  def atomsymb: Parser[String] = """[a-zA-Z][a-zA-Z0-9_]*""".r
  def term: Parser[FOLTerm] = function | constant | variable
  def function: Parser[FOLTerm] = conssymb ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Function(ConstantStringSymbol(x), params.asInstanceOf[List[FOLTerm]])}
  def constant: Parser[FOLConst] = conssymb ^^ {case x => FOLFactory.createVar(ConstantStringSymbol(x), Ti()).asInstanceOf[FOLConst]}
  def variable: Parser[FOLVar] = varsymb ^^ {case x => FOLFactory.createVar(VariableStringSymbol(x), Ti()).asInstanceOf[FOLVar]}
  def topbottom: Parser[FOLFormula] = "$" ~> ( "T" ^^ (x=> topformula) | "F" ^^ (x => bottomformula) )

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
    val freevars = f.getFreeAndBoundVariables._1.toList
    val pairs : List[(Var,FOLExpression)] = (freevars zip (0 to (freevars.size-1))) map (x => (x._1,  x._1.factory.createVar(VariableStringSymbol("v"+x._2), x._1.exptype).asInstanceOf[FOLExpression]) )
    val nf : FOLFormula = Substitution(pairs)(f).asInstanceOf[FOLFormula]

    normalizeFormula(nf,freevars.size)._1
  }

  def normalizeFormula[T <: LambdaExpression](f:T, i:Int) : (T, Int) = f match {
    case Var(name, exptype) => (f, i)
    case App(s, t) =>
      val (s_, i_) = normalizeFormula(s,i)
      val (t_, j) = normalizeFormula(t,i)
      (s.factory.createApp(s_, t_).asInstanceOf[T], j)
    case Abs(x, s) =>
      val x_ = x.factory.createVar(VariableStringSymbol("v"+i), x.exptype)
      val sub = Substitution[LambdaExpression]((x, x_))
      val (s_, j) = normalizeFormula(sub(s).asInstanceOf[T], i+1)
      (s.factory.createAbs(x_, s_).asInstanceOf[T], j)
    case _ => throw new Exception("Unhandled expression type in variable normalization!")
  }

}

