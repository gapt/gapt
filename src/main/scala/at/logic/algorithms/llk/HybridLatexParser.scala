package at.logic.algorithms.hlk

import at.logic.parsing.language.hlk.{ast, DeclarationParser}
import at.logic.parsing.language.hlk.ast.LambdaAST
import scala.util.parsing.input.PagedSeqReader
import scala.collection.immutable.PagedSeq
import java.io.FileReader
import at.logic.language.lambda.types.TA
import at.logic.language.hol._
import at.logic.calculi.lk.base.{FSequent, LKProof}
import at.logic.parsing.language.xml.ProofDatabase
import at.logic.algorithms.llk.TokenToLKConverter


/**
 *  An extended proof database allows to label subproofs by formulas. It provides mappings from formulas to proofs
 * additionally to the list of pairs. */
case class ExtendedProofDatabase(eproofs : Map[HOLFormula, LKProof],
                                 eaxioms : Map[HOLFormula,HOLFormula],
                                 edefinitions : Map[HOLExpression, HOLExpression])
  extends ProofDatabase(Map(),Nil,Nil,Nil) {
  override val proofs : List[(String,LKProof)] = eproofs.map(x =>
    x._1 match {
      case Atom(HOLConst(sym,_),_) => (sym.toString, x._2)
      case Atom(HOLVar(sym,_),_) => (sym.toString, x._2)
    }).toList
  override val Definitions : Map[HOLExpression, HOLExpression] = edefinitions
  override val axioms : List[FSequent] = eaxioms.values.toList map (x => FSequent(Nil, x::Nil))
  override val sequentLists : List[(String,List[FSequent])] = Nil
}

/**
 * The abstract class for tokens of an llk proof. TTokens represent type declarations, ATokens represent axiom
 * and definition declarations, and RTokens represent a rule inference.
 */
abstract class Token

/**
 * A TToken represents an LLK type declaration.
 * @param decltype either "VARDEC" or "CONSTDEC"
 * @param names a list of symbol names
 * @param types the assigned type
 */
case class TToken(decltype : String, names : List[String], types : TA ) extends Token

/**
 * An AToken represents an Axiom declaration or Definition declaration.
 * @param rule either "AXIOMDEF", "PREDDEF" or"FUNDEF"
 * @param name the (unique) name of the definition/axiom
 * @param antecedent the antecedent of the declaration sequent (not yet typechecked)
 * @param succedent the succedent of the declaration sequent (not yet typechecked)
 */
case class AToken(rule:String, name : Option[LambdaAST], antecedent: List[LambdaAST], succedent:List[LambdaAST]) extends Token

/**
 * A RToken represents a rule application.
 * @param rule One out of "AX", "ALLL", "ALLR", "EXL", "EXR", "ANDL", "ANDR", "ORL", "ORR", "IMPL", "IMPR", "NEGL",
 *             "NEGR", "CUT", "EQL", "EQR", "WEAKL", "WEAKR", "CONTRL", "CONTRR", "DEF", "BETA", "INSTAXIOM"
 * @param name quantifier rules allow optional specification of the subsitution term, definitions and axiom instantiations
 *             take the referenced declaration, etc.
 * @param antecedent the antecedent of the declaration sequent (not yet typechecked)
 * @param succedent the antecedent of the declaration sequent (not yet typechecked)
 * @param sub some rules like axiom instantiation specify substitutions, which are passed as list of var-term pairs
 */
case class RToken(rule:String, name : Option[LambdaAST],  antecedent: List[LambdaAST],
                     succedent:List[LambdaAST], sub:List[(ast.Var,LambdaAST)]) extends Token


class HybridLatexParserException(m : String, t: Throwable) extends Exception(m, t) {
  def this(m: String) = this(m, null)
}

/**
 * This code works around some limitations of latex syntax and adds alternative syntax for abstraction, application and
 * adds support of some macros used in the n-tape proof.
 */
trait LatexReplacementParser extends DeclarationParser {
  override lazy val abs : PackratParser[LambdaAST] =
    ("\\lambda" ~ atom2 ~ formula) ^^ { case _ ~ v ~ f => ast.Abs(v, f) }



  override lazy val appOrAtomWeq : PackratParser[LambdaAST] =
    (parens("@" ~> rep1(formula)) |
      ("\\apply" ~> "{" ~> rep1(formula) <~ "}"))  ^^ { x => x match {
      case List(elem) => elem
      case list => ast.App(list)
    }
    } | atomWeq

  lazy val latexmacros : PackratParser[LambdaAST] =
    ("\\ite{" ~> formula <~ "}") ~ ("{" ~> formula <~ "}") ~ ("{" ~> formula <~ "}") ^^ {
      case f1 ~ f2 ~ f3 => ast.App(List(ast.Var("ite"),f1,f2,f3))
    } |
      ("\\benc{" ~> formula <~ "}") ^^ {
        case f1  => ast.App(List(ast.Var("be"),f1))
      }|
      ("\\ienc{" ~> formula <~ "}") ^^ {
        case f1  => ast.App(List(ast.Var("ie"),f1))
      }

  override lazy val atom : PackratParser[LambdaAST] =
    latexmacros | atom1 | atom2 | topbottom

  override lazy val iatom2 : PackratParser[LambdaAST] = iatom3 ~ """([+\-]|\\bm)""".r  ~ iatom3 ^^ { _ match {
    case t1 ~ "\\bm" ~ t2  => ast.App(List(ast.Var("bm"), t1, t2) ) //TODO: change to \dotdiv and modify prooftool etc
    case t1 ~ sym ~ t2  => ast.App(List(ast.Var(sym), t1, t2) )
  }
  } | iatom3


  //accept latex connectives
  override lazy val implication: PackratParser[LambdaAST]  = (dis_or_con ~ ("<->"|"->"|"<-"|"\\impl") ~ dis_or_con) ^^ { _ match {
    case f ~ "->"  ~ g => ast.Imp(f,g)
    case f ~ "\\impl"  ~ g => ast.Imp(f,g)
    case f ~ "<-"  ~ g => ast.Imp(g,f)
    case f ~ "<->" ~ g => ast.And(ast.Imp(f,g), ast.Imp(g,f))
  }} | dis_or_con

  override lazy val disjunction: PackratParser[LambdaAST]  =
    (conlit ~ (("|" | "\\lor") ~> disjunction) ^^ {case f ~ g => ast.Or(f,g)}) | conlit

  override lazy val conjunction: PackratParser[LambdaAST]  =
    ( qliteral ~ (("&" | "\\land") ~> conjunction)   ^^ { case f ~ g => ast.And(f,g) }) | qliteral

  override lazy val allformula_ : PackratParser[LambdaAST]   =
    (("all" | "\\forall")    ~> atom2 ~ ( allformula_ | exformula_ | formula) ) ^^ {case v ~ f => ast.All(v,f) }

  override lazy val exformula_ : PackratParser[LambdaAST]    =
    (("exists" | "\\exists") ~> atom2 ~ ( allformula_ | exformula_ | formula) ) ^^ { case v ~ f => ast.Exists(v,f) }

  override lazy val negation:PackratParser[LambdaAST] =
    (("""(-|\\neg)""".r) ~> literal2 ^^ { x => ast.Neg(x) }) | absOrAtomWeq

  lazy val reservedset = Set("\\neg","\\land","\\lor","\\impl","\\forall","\\exists")
  override lazy val atomsymb: Parser[String] = atomsymb2 ^? (
    { case x if ! (reservedset contains x)  => x },
    (x => "error: \\neg,\\land,\\lor,\\impl,\\forall,\\exists are reserved names")
  )

  lazy val atomsymb2: Parser[String] = atomregexp


}

object HybridLatexParser extends HybridLatexParser
class HybridLatexParser extends DeclarationParser with LatexReplacementParser with TokenToLKConverter {

  def parseFile(fn : String) : List[Token] = {
    val reader = new PagedSeqReader(new PagedSeq[Char](new FileReader(fn).read))

    parseAll( rules, reader) match {
      case Success(r, _) => r
      case NoSuccess(msg, input) =>
        throw new HybridLatexParserException("Error parsing Hybrid Latex/LK in "+fn+" at position "+input.pos +": "+msg)
    }
  }

  def parse(in : CharSequence) : List[Token] = {
    parseAll( rules, in) match {
      case Success(r, _) => r
      case NoSuccess(msg, input) =>
        throw new HybridLatexParserException("Error parsing Hybrid Latex/LK at position "+input.pos +": "+msg)
    }
  }

  override def d[T](r:T) :T = { println(r);  r}

  lazy val rules : PackratParser[List[Token]] = rep1((rule1|rule2|rule3|decl|comment) )

  lazy val comment : PackratParser[RToken] =  ("%" ~> "[^%]*".r <~ "%") ^^ { _ =>
    RToken("COMMENT", None, Nil, Nil, Nil)
  }

  lazy val rule1 : PackratParser[RToken] = (("\\" ~> "CONTINUEWITH" <~ "{" ) ~ atom  <~ "}" ) ^^ {
    _ match {
      case cw ~ atom  => RToken(cw, Some(atom), Nil, Nil, Nil)
    }
  }

  lazy val rule2 : PackratParser[Token] = ("\\" ~>
    "(AX|AND[LR]|OR[LR]|IMP[LR]|NEG[LR]|EQ[LR]|WEAK[LR]|CONTR[LR]|CUT|DEF|BETA|PREDDEF|FUNDEF|TAUTCOMPLETION|AUTOPROP)".r
    <~ "{") ~ (repsep(formula, ",") <~ "}") ~ ("{" ~> repsep(formula,",") <~ "}") ^^ { _ match {
      case (name@"PREDDEF") ~ de ~ to => AToken(name, None, de, to)
      case (name@"FUNDEF") ~ de ~ to => AToken(name, None, de, to)
      case name ~ antecedent ~ succedent => RToken(name, None, antecedent, succedent, Nil)
    }
  }

  lazy val rule3 : PackratParser[Token] = rule3a | rule3b

  lazy val rule3a : PackratParser[Token] = ("\\" ~> "(ALL[LR]|EX[LR]|INSTLEMMA|CONTINUEFROM|AXIOMDEC)".r
    <~ "{" <~ "([^}]+:)?".r ) ~ (opt(formula) <~ "}") ~ ("{" ~> repsep(formula,",") <~ "}") ~ ("{" ~> repsep(formula,",") <~ "}")  ^^ { _ match {
    case (name@"AXIOMDEC") ~ arg1 ~ antecedent ~ succedent => AToken(name, arg1, antecedent, succedent)
    case name ~ arg1 ~ antecedent ~ succedent => RToken(name, arg1, antecedent, succedent, Nil)
  }
  }

  lazy val rule3b : PackratParser[Token] = ("\\" ~> "(INSTAXIOM|EQAXIOM)".r
    <~ "{") ~ (opt("([^:}]+:)?".r ) ~> opt("sub" ~> parens(substitution))) ~ (opt(formula) <~ "}") ~
    ("{" ~> repsep(formula,",") <~ "}") ~ ("{" ~> repsep(formula,",") <~ "}")  ^^ { _ match {
    case name  ~ Some(sub)~ arg1 ~ antecedent ~ succedent => /* println("Parsed sub:"+sub); */ RToken(name, arg1, antecedent, succedent, sub)
    case name ~ None ~ arg1 ~ antecedent ~ succedent => RToken(name, arg1, antecedent, succedent, Nil)
  }
  }

  lazy val substitution: PackratParser[List[(ast.Var, ast.LambdaAST)]] = rep1sep( single_substitution, "," )
  lazy val single_substitution: PackratParser[(ast.Var, ast.LambdaAST)] =
    (atomsymb ~ ("=" ~> formula)) ^^ { case x ~ y => (ast.Var(x),y)}


  lazy val decl : PackratParser[TToken] = ("\\" ~> "(CONSTDEC|VARDEC)".r <~ "{") ~
    (rep1sep(symbolnames, ",") <~ "}") ~ ("{" ~> complexType <~ "}") ^^ { _ match {
    case "CONSTDEC" ~ namest ~ (types:TA) => TToken("CONST", namest, types)
    case "VARDEC" ~ namest ~ (types:TA) => TToken("VAR", namest, types)
  }
  }


  def splitAtOutermostComma(s:String) : List[String] = splitAtOutermostComma(s, "", List(), 0).reverse
  def splitAtOutermostComma(s:String, current : String, acc : List[String], level : Int) : List[String] = {
    if (s.isEmpty) {
      require(level == 0, "Problem splitting a list of formulas apart: there are still "+level+" parenthesis left open!")
      if (current.isEmpty) acc else current::acc
    } else {
      s.head match {
        case '(' =>
          splitAtOutermostComma(s.tail, current+s.head, acc, level + 1 )
        case ')' =>
          require(level > 0, "Problem splitting a list of formulas apart: trying to close parenthesis without corresponding open one! "+s)
          splitAtOutermostComma(s.tail, current+s.head, acc, level - 1 )
        case ',' if (level == 0) =>
          splitAtOutermostComma(s.tail, "", current::acc, level)
        case _ =>
          splitAtOutermostComma(s.tail, current+s.head, acc, level )
      }
    }

  }

}

