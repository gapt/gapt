package at.logic.parsing.language.hlk

import util.parsing.combinator.JavaTokenParsers
import scala.util.parsing.combinator.PackratParsers

import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.hol._
import at.logic.language.lambda.types._
import at.logic.language.fol

/**
 * Extension of prover9 parser to hol
 */

//Abstract syntax tree - ignores typing
package ast {
  abstract class LambdaAST {
    def varnames : List[String]
  };

  case class Var(name : String) extends LambdaAST { def varnames = List(name) }
  case class App(args: List[LambdaAST]) extends LambdaAST { def varnames = args.foldLeft[List[String]](Nil)((x,e) => x ++ e.varnames)  }
  case class Abs(v : Var, t : LambdaAST) extends LambdaAST { def varnames = v.name :: t.varnames }
  case class All(v : Var, t : LambdaAST) extends LambdaAST { def varnames = v.name :: t.varnames }
  case class Exists(v : Var, t : LambdaAST) extends LambdaAST { def varnames = v.name :: t.varnames }
  case class Neg(t : LambdaAST) extends LambdaAST { def varnames = t.varnames }
  case class And(l : LambdaAST, r : LambdaAST) extends LambdaAST { def varnames = l.varnames ++ r.varnames }
  case class Or(l : LambdaAST, r : LambdaAST) extends LambdaAST { def varnames = l.varnames ++ r.varnames }
  case class Eq(l : LambdaAST, r : LambdaAST) extends LambdaAST { def varnames = l.varnames ++ r.varnames }
  case class Imp(l : LambdaAST, r : LambdaAST) extends LambdaAST { def varnames = l.varnames ++ r.varnames }
  case class Top() extends  LambdaAST { def varnames = Nil }
  case class Bottom() extends LambdaAST {def varnames = Nil }
}


object HOLASTParser extends HOLASTParser;

//Parser from strings to ast
class HOLASTParser extends JavaTokenParsers with PackratParsers {
  import ast.LambdaAST
  /* debug transformers */
  def d[T](s:String,f:T) : T = { println(s+": "+f); f }
  def d[T](f:T) : T = d("(debug)",f)

  /* The main entry point to the parser for prover9 formulas. To parse literals, use literal as the entry point. */
  def parseFormula(s:String) : LambdaAST = parseAll(formula, s) match {
    case Success(result, _) => result
    case NoSuccess(msg, input) =>
      throw new Exception("Error parsing HOL formula '"+s+"' at position "+input.pos+". Error message: "+msg)
  }

  lazy val pformula : PackratParser[LambdaAST] = parens(formula) | allformula | exformula
  lazy val formula: PackratParser[LambdaAST] = implication ^^ flattenApps
  //precedence 800
  lazy val implication: PackratParser[LambdaAST]  = (dis_or_con ~ ("<->"|"->"|"<-") ~ dis_or_con) ^^ { _ match {
    case f ~ "->"  ~ g => ast.Imp(f,g)
    case f ~ "<-"  ~ g => ast.Imp(g,f)
    case f ~ "<->" ~ g => ast.And(ast.Imp(f,g), ast.Imp(g,f))
  }} | dis_or_con

  lazy val dis_or_con: PackratParser[LambdaAST] = (disjunction | conlit )
  //precedence 790
  lazy val disjunction: PackratParser[LambdaAST]  =
    (conlit ~ ("|" ~> disjunction) ^^ {case f ~ g => ast.Or(f,g)}) | conlit

  //precedence 780
  lazy val conlit: PackratParser[LambdaAST] =  (conjunction| qliteral )
  lazy val conjunction: PackratParser[LambdaAST]  =
    ( qliteral ~ ("&" ~> conjunction)   ^^ { case f ~ g => ast.And(f,g) }) | qliteral
  //precedence 750
  lazy val qliteral : PackratParser[LambdaAST] = allformula | exformula | literal2
  lazy val allformula : PackratParser[LambdaAST] = parens(allformula_)
  lazy val exformula : PackratParser[LambdaAST] = parens(exformula_)
  lazy val allformula_ : PackratParser[LambdaAST]   =
    ("all"    ~> atom2 ~ ( allformula_ | exformula_ | formula) ) ^^ {case v ~ f => ast.All(v,f) }

  lazy val exformula_ : PackratParser[LambdaAST]    =
    ("exists" ~> atom2 ~ ( allformula_ | exformula_ | formula) ) ^^ { case v ~ f => ast.Exists(v,f) }

  //precedence 300
  lazy val literal2:PackratParser[LambdaAST] = absOrAtomWeq | negation
  lazy val negation:PackratParser[LambdaAST] = ("-" ~> literal2 ^^ { x => ast.Neg(x) }) | absOrAtomWeq


  def parens[T](p:Parser[T]) : Parser[T] = "(" ~> p <~ ")"
  //precedence 250
  lazy val absOrAtomWeq : PackratParser[LambdaAST] = parens(abs) | appOrAtomWeq
  lazy val abs : PackratParser[LambdaAST] =
    ("\\" ~ atom2 ~ ("=>" ~> formula)) ^^ { case _ ~ v ~ f => ast.Abs(v, f) }

  //precedence 200
  lazy val appOrAtomWeq : PackratParser[LambdaAST] =
    parens("@" ~> rep1(formula))  ^^ {_ match {
      case List(elem) => elem
      case list => ast.App(list)
   }
  } | atomWeq

  lazy val atomWeq: PackratParser[LambdaAST] =  eqatom | atom

  //infixatom
  lazy val eqatom : PackratParser[LambdaAST] = iatom1 ~ """(!?=)""".r  ~ iatom1 ^^ {
    _ match {
      case t1 ~ "=" ~ t2  => ast.Eq(t1,t2)
      case t1 ~ "!=" ~ t2 => ast.Neg(ast.Eq(t1,t2))
    }
  } | iatom1

  lazy val iatom1 : PackratParser[LambdaAST] = iatom2 ~ """((<|>)=?)""".r  ~ iatom2 ^^ {
      case t1 ~ sym ~ t2  => ast.App(List(ast.Var(sym), t1, t2) )
  } | iatom2


  lazy val iatom2 : PackratParser[LambdaAST] = iatom3 ~ """[+\-]""".r  ~ iatom3 ^^ {
    case t1 ~ sym ~ t2  => ast.App(List(ast.Var(sym), t1, t2) )
  } | iatom3

  lazy val iatom3 : PackratParser[LambdaAST] = pfiatom ~ """[*/]""".r  ~ pfiatom ^^ {
    case t1 ~ sym ~ t2  => ast.App(List(ast.Var(sym), t1, t2) )
  } | pfiatom

  lazy val pfiatom = pformula | atom

  lazy val atom: PackratParser[LambdaAST] = atom1 | atom2 | topbottom
  lazy val atom1: PackratParser[LambdaAST] = atomsymb ~ parens(repsep(formula,",")) ^^ {
    case x ~ params => ast.App(ast.Var(x) :: params )}
  lazy val atom2: PackratParser[ast.Var] = atomsymb ^^ {case x =>  ast.Var(x) }

  lazy val atomsymb: Parser[String] = atomregexp
  lazy val atomregexp = """(\\?)([a-zA-Z0-9']+([_^](\{[a-zA-Z0-9']+\})?)*(\[[a-zA-Z0-9']+\])*)+""".r

  lazy val topbottom: PackratParser[LambdaAST] = "$" ~> ( "T" ^^ (x=> ast.Top()) | "F" ^^ (x =>  ast.Bottom()) )


  def flattenApps(f : ast.LambdaAST) : ast.LambdaAST = f match {
    case ast.App( ast.App(list) :: rest   ) =>  ast.App( ((list ++ rest) map flattenApps)  )
    case ast.App(Nil) => throw new Exception("Applications need at least one parameter!")

    case ast.Abs(x,t) => ast.Abs(x, flattenApps(t) )
    case ast.All(x,t) => ast.All(x, flattenApps(t))
    case ast.And(l,r) => ast.And( flattenApps(l), flattenApps(r))
    case ast.Eq(l,r) => ast.Eq( flattenApps(l), flattenApps(r))
    case ast.Exists(x,t) => ast.Exists(x, flattenApps(t))
    case ast.Imp(l,r) => ast.Imp(flattenApps(l), flattenApps(r))
    case ast.Neg(l) => ast.Neg( flattenApps(l))
    case ast.Or(l,r) => ast.Or(flattenApps(l), flattenApps(r))
    case _ => f //handles Top, Bottom, Var
  }
}

object DeclarationParser extends DeclarationParser;

class DeclarationParser extends HOLASTParser {
  /* The main entry point to the parser for prover9 formulas. To parse literals, use literal as the entry point. */
  def parseDeclaration(s:String) : Map[String, HOLExpression] = parseAll(declaration_list, s) match {
    case Success(result, _) => result
    case NoSuccess(msg, input) =>
      throw new Exception("Error parsing type declaration '"+s+"' at position "+input.pos+". Error message: "+msg)
  }

  lazy val symbolnames = atomregexp | """((<|>)=?)|(!?=)|[+\-*]""".r

  // simple and complex types
  lazy val ti : PackratParser[TA] = "i" ^^ { _ => Ti }
  lazy val to : PackratParser[TA] = "o" ^^ { _ => To }
  lazy val simpleType : PackratParser[TA] = ti | to
  lazy val complexType : PackratParser[TA]= ((complexType | parens(complexType)) ~ ">" ~ (complexType|parens(complexType))) ^^ { case t1 ~ _ ~ t2 => t1 -> t2} | simpleType

  lazy val constdecl : PackratParser[Map[String, HOLExpression] ] = "const" ~ rep1sep(symbolnames, ",") ~ ":" ~ complexType ^^ {
    case _ ~ varnames ~ _ ~ exptype => Map[String, HOLExpression]() ++ ( varnames map (x => (x, HOLConst(x, exptype))))
  }

  lazy val vardecl : PackratParser[Map[String, HOLExpression] ] = "var" ~ rep1sep(symbolnames, ",") ~ ":" ~ complexType ^^ {
    case _ ~ varnames ~ _ ~ exptype => Map[String, HOLExpression]() ++ ( varnames map (x => (x, HOLVar(x, exptype))))
  }

  //declaration lists e.g.: var x,y :i; const a,b : i; const P : i > i > o
  lazy val declaration : PackratParser[Map[String, HOLExpression] ]= constdecl | vardecl
  lazy val declaration_list : PackratParser[Map[String, HOLExpression] ] =
    (rep1sep(declaration, ";") ~ ";") ^^ { case l ~ _ =>  l.foldLeft(defaultsymbols)( (map, x) => {
      for (v <- map.keys) {
        require(!x.contains(v), "Redeclaration of the variable "+v+" is not allowed!" )
      }
      map ++ x })
    }

  val defaultsymbols = Map[String, HOLExpression]()

  lazy val declaredformula : PackratParser[(Map[String, HOLExpression], ast.LambdaAST)]  =
    (declaration_list ~ formula) ^^ { case d ~ f => (d,f) }
}


object HLKHOLParser extends HLKHOLParser
class HLKHOLParser {
  //automated casting, a bit dirty
  private def f(e:HOLExpression) : HOLFormula = {
    require(e.isInstanceOf[HOLFormula], "The expression "+e+" is supposed to be a formula!")
    e.asInstanceOf[HOLFormula]
  }
  private def v(e:HOLExpression) : HOLVar = {
    require(e.isInstanceOf[HOLVar], "The expression "+e+" is supposed to be a variable!")
    e.asInstanceOf[HOLVar]
  }

  def ASTtoHOLnormalized( create : String => HOLExpression, exp : ast.LambdaAST  ) : HOLExpression =
    BetaReduction.betaNormalize(ASTtoHOL(create,exp))

  //converts an ast to a holformula. create decides if the string represents a constant or variable of appropriate type
  // and returns the matching hol expression
  def ASTtoHOL( create : String => HOLExpression, exp : ast.LambdaAST  ) : HOLExpression = exp match {
    case ast.Abs(ast.Var(x),t) => HOLAbs(v(create(x)), ASTtoHOL(create, t))
    case ast.All(ast.Var(x), t) => AllVar(v(create(x)), f(ASTtoHOL(create, t)))
    case ast.Exists(ast.Var(x), t) => ExVar(v(create(x)), f(ASTtoHOL(create, t)))

    case ast.Neg(l) => Neg(f(ASTtoHOL(create, l)))

    case ast.App(Nil) => throw new Exception("Empty applications are not accepted!")
    case ast.App(first::Nil) => ASTtoHOL(create, first)
    case ast.App(first::rest) =>
      //require(! rest.isEmpty, "Empty applications are not accepted!");
      rest.foldLeft(ASTtoHOL(create, first))( (exp, a) => HOLApp(exp, ASTtoHOL(create, a)))

    case ast.And(l,r) => And(f(ASTtoHOL(create, l)), f(ASTtoHOL(create,r)))
    case ast.Or(l,r) => Or(f(ASTtoHOL(create, l)), f(ASTtoHOL(create,r)))
    case ast.Imp(l,r) => Imp(f(ASTtoHOL(create, l)), f(ASTtoHOL(create,r)))

    case ast.Eq(l,r) => Equation(ASTtoHOL(create, l), ASTtoHOL(create,r))

    case ast.Var(x) => create(x)
    case ast.Top() => Atom(TopC, Nil )
    case ast.Bottom() => Atom(BottomC, Nil)
  }

  def parse(create : String => HOLVar, s : CharSequence) : HOLExpression = {
    DeclarationParser.parseAll(DeclarationParser.formula, s) match {
      case DeclarationParser.Success(result, _) => ASTtoHOL(create, result)
      case DeclarationParser.NoSuccess(msg, input) =>
        throw new Exception("Error parsing HOL formula '"+s+"' at position "+input.pos+". Error message: "+msg)
    }

  }

  def parse(s : CharSequence) : HOLExpression = {
    DeclarationParser.parseAll(DeclarationParser.declaredformula, s) match {
      case DeclarationParser.Success((declarations, tree), _) =>
        ASTtoHOL(x => declarations(x), tree)
      case DeclarationParser.NoSuccess(msg, input) =>
        throw new Exception("Error parsing HOL formula '"+s+"' at position "+input.pos+". Error message: "+msg)
    }

  }

  def parseFormula(s : String) : HOLExpression = f(parse(s))


}


