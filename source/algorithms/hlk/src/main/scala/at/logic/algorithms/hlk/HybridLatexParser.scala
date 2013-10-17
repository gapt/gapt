package at.logic.algorithms.hlk

import at.logic.parsing.language.hlk.{ast, DeclarationParser, HLKHOLParser}
import at.logic.parsing.language.hlk.ast.LambdaAST
import scala.util.parsing.input.PagedSeqReader
import scala.collection.immutable.PagedSeq
import java.io.FileReader
import at.logic.language.lambda.types.TA
import at.logic.language.hol._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.base.{LKProof, FSequent}
import at.logic.utils.ds.acyclicGraphs.AGraph
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.algorithms.matching.fol.FOLMatchingAlgorithm
import at.logic.algorithms.matching.hol.NaiveIncompleteMatchingAlgorithm

abstract class Token
case class RToken(rule:String, name : Option[LambdaAST], antecedent: List[LambdaAST], succedent:List[LambdaAST]) extends Token
case class TToken(decltype : String, names : List[String], types : TA ) extends Token

//case class QToken(override val rule:String, override val name : LambdaAST, override val antecedent: List[LambdaAST], override val succedent:List[LambdaAST], term : LambdaAST)
//  extends RToken(rule, name, antecedent, succedent)

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

}

object HybridLatexParser extends HybridLatexParser
class HybridLatexParser extends DeclarationParser with LatexReplacementParser with TokenToLKConverter {

  def parseFile(fn : String) : List[Token] = {
    val reader = new PagedSeqReader(new PagedSeq[Char](new FileReader(fn).read))

    parseAll( rules, reader) match {
      case Success(r, _) => r
      case NoSuccess(msg, input) =>
        throw new Exception("Error parsing Hybrid Latex/LK in "+fn+" at position "+input.pos +": "+msg)
    }
  }

  def parse(in : CharSequence) : List[Token] = {
    parseAll( rules, in) match {
      case Success(r, _) => r
      case NoSuccess(msg, input) =>
        throw new Exception("Error parsing Hybrid Latex/LK at position "+input.pos +": "+msg)
    }
  }

  override def d[T](r:T) :T = { println(r);  r}

  lazy val rules : PackratParser[List[Token]] = rep1((rule1|rule2|rule3|decl|comment) )

  lazy val comment : PackratParser[RToken] =  ("%" ~> "[^%]*".r <~ "%") ^^ { _ =>
    RToken("COMMENT", None, Nil, Nil)
  }

  lazy val rule1 : PackratParser[RToken] = (("\\" ~> "CONTINUEWITH" <~ "{" ) ~ atom  <~ "}" ) ^^ {
    _ match {
      case cw ~ atom  => RToken(cw, Some(atom), Nil, Nil)
    }
  }

  lazy val rule2 : PackratParser[RToken] = ("\\" ~>
    "(AX|AND[LR]|OR[LR]|IMP[LR]|NEG[LR]|EQ[LR]|WEAK[LR]|CONTR[LR]|CUT|DEF|BETA)".r
    <~ "{") ~ (repsep(formula, ",") <~ "}") ~ ("{" ~> repsep(formula,",") <~ "}") ^^ {
    case name ~ antecedent ~ succedent => RToken(name, None, antecedent, succedent)
  }


  lazy val rule3 : PackratParser[RToken] = ("\\" ~> "(ALL[LR]|EX[LR]|INSTLEMMA|INSTAXIOM|CONTINUEFROM|EQAXIOM)".r
    <~ "{" <~ "([^}]+:)?".r ) ~ (opt(formula) <~ "}") ~ ("{" ~> repsep(formula,",") <~ "}") ~ ("{" ~> repsep(formula,",") <~ "}")  ^^ {
    case name ~ arg1 ~ antecedent ~ succedent => RToken(name, arg1, antecedent, succedent)
  }

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

trait TokenToLKConverter {
  def createNaming(r : List[Token]) : (String => HOLExpression) = {
    val ctypes : List[(String,TA)] = r.flatMap(_ match {
      case TToken("CONST",names,t) => names map ((_,t))
      case _ => Nil
    })
    val constmap = Map[String, TA]() ++ ctypes

    val vtypes : List[(String,TA)] = r.flatMap(_ match {
      case TToken("VAR",names,t) => names map ((_,t))
      case _ => Nil
    })
    val varmap = Map[String, TA]() ++ vtypes

    { (s:String)=> {
      if (varmap contains s) {
        HOLVar(VariableStringSymbol(s), varmap(s))
      } else

      if (constmap contains s) {
        HOLConst(ConstantStringSymbol(s), constmap(s))
      } else

        throw new Exception("no type declaration for symbol "+s)
    }}
  }


  def printRules(r: List[Token]) : List[FSequent]= {
    val rules = r.filter( _ match { case RToken(_,_,_,_) => true; case _ => false}  )
    val naming = createNaming(r)

    var l = List[FSequent]()

    for (RToken(name, argname, antecedent, succedent) <- rules) {
      val ant = antecedent.map(x => c(HLKHOLParser.ASTtoHOL( naming  ,x)))
      val suc = succedent.map(x  => c(HLKHOLParser.ASTtoHOL( naming  ,x)))
      val fs = FSequent(ant, suc)
      println(name + ": "+fs)
      l = fs  :: l
    }

    l.reverse
  }


  def createLKProof( l : List[Token]) : LKProof = {
    val (rtokens, ttokens) = l.partition( _ match {
      case RToken(_,_,_,_) =>  true ;
      case TToken(_,_,_) => false; }
    ).asInstanceOf[(List[RToken], List[TToken])] //need to cast because partition returns Tokens
    val naming = createNaming(ttokens)

    val (last,rm) = rtokens.foldLeft((List[RToken]()), Map[HOLFormula, List[RToken] ]()) ((current, token) => {
      token match {
        case RToken("CONTINUEWITH", Some(name), a, s) =>
          //put proof under name into map, continue with empty rulelist
          try {
            val nformula = c(HLKHOLParser.ASTtoHOL(naming, name))
            ( Nil, current._2 + ((nformula,current._1)) )
          } catch {
            case e:Exception => throw new Exception("Error in parsing CONTINUEWITH{"+name+"}{"+a+"}{"+s"}: "+e.getMessage, e)
          }
        case RToken("CONTINUEWITH", _,_,_) =>
          throw new Exception("The CONTINUEWITH statement needs a name giving the argument!")
        case RToken("COMMENT",_,_,_) =>
          //filter comments
          current
        case _ =>
          //apend rule to current list
          ( token::current._1, current._2 )
      }
    })

    require(last.isEmpty, "There are some rules left after parsing the list, use CONTINUEFROM to give proof a name! "+last)

    val dependecies = getDependecyMap(naming, rm)
    //dependecies map (x => println(x._1.toPrettyString+": "+x._2.mkString(",")))
    val ordering : List[HOLFormula] = getOrdering(dependecies)
    println((ordering map (_.toPrettyString)).mkString("Ordering: ",", ",""))

    var current_proof : List[LKProof] = List[LKProof]()


    /*

    for ( RToken(name, auxterm, antecedent, succedent) <- rtokens) {
      val ant = antecedent.map(x => c(HLKHOLParser.ASTtoHOL( naming  ,x)))
      val suc = succedent.map(x  => c(HLKHOLParser.ASTtoHOL( naming  ,x)))
      val fs = FSequent(ant, suc)
      name match {
        case "AX" =>
          current_proof = Axiom(ant, suc) :: current_proof
        case "ALLL" =>
          require(current_proof.size > 0, "Imbalanced proof tree in application of "+name+" with es: "+fs)
          require(auxterm.isDefined, "Weak quantfier rule "+name+" requires the substitution term to be passed as an argument!")
          val oldproof = current_proof.head
          val (main, List(aux)) = filterContext(oldproof.root.toFSequent, fs)
          val term = HLKHOLParser.ASTtoHOL(naming,auxterm.get)
          val rule = ForallLeftRule(oldproof, aux, main, term  )
          current_proof = rule :: current_proof.tail
      }
    }

    //println(current_proof)
    */
    //current_proof.head
    Axiom(Nil,Nil)
  }


  def getOrdering[T](pm : Map[T, List[T]]) : List[T] = {
    val (leaves, nonleaves) = pm.partition( el => el._2.isEmpty )
    require(leaves.nonEmpty, "Circular dependency in prooflinks detected: "+pm)
    val leaflist = leaves.keySet.toList
    if (nonleaves.isEmpty) {
      leaflist
    } else {
      //remove leaves from the graph
      val rest = nonleaves map ( el => (el._1, el._2 filterNot(leaflist contains _)))
      leaflist ++ getOrdering(rest)
    }
  }

  def getDependecyMap(naming : String => HOLExpression,pm : Map[HOLFormula, List[RToken]]) : Map[HOLFormula,List[HOLFormula]] = {
    val proofnames = pm.keySet.toList
    // only keep continuefrom tokens in the lists, map to the formulas in
    // the proofnames against which the dependencies matches
    pm.map( element =>
      (element._1, element._2.flatMap( _ match {
        case RToken("CONTINUEFROM",Some(f),_,_) =>
          //find the matching proofs
          proofnames.filter( p =>
            NaiveIncompleteMatchingAlgorithm.holMatch(p, c(HLKHOLParser.ASTtoHOL(naming, f)))(Nil).isDefined
          ) match {
            //and check if the dependency is ok
            case Nil =>
              throw new Exception("Could not find a matching dependency for proof "+f
                +" in: "+proofnames.mkString(","))
            case l@List(d) =>
              l
            case _ =>
              throw new Exception("Found more than one matching dependency for proof "+f
                +" in: "+proofnames.mkString(",")+" but proof links need to be unique!")
          }

        case RToken("CONTINUEFROM",_,_,_) =>
          throw new Exception("The CONTINUEFROM statement needs a proof as an argument!")
        case _ => Nil
      }))
    )
  }


  def filterContext(fs_old : FSequent, fs_new : FSequent) : (HOLFormula, List[HOLFormula]) = {
    val FSequent(aold, sold) = fs_old
    val FSequent(anew, snew) = fs_new
    val adiffn = anew diff aold
    val sdiffn = snew diff sold

    val adiffo = aold diff anew
    val sdiffo = sold diff snew

    val ndiff = adiffn ++ sdiffn
    val odiff = adiffo ++ sdiffo

    require(ndiff.length == 1, "We want exactly one primary formula, not: "+ndiff)
    require(odiff.length > 0, "We want at least one auxiliary formula, not: "+odiff)
    (ndiff(0), odiff.toList)

  }



  private def c(e:HOLExpression) : HOLFormula =
    if (e.isInstanceOf[HOLFormula]) e.asInstanceOf[HOLFormula] else
      throw new Exception("Could not convert "+e+" to a HOL Formula!")

}
