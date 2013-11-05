package at.logic.algorithms.hlk

import at.logic.parsing.language.hlk.{ast, DeclarationParser, HLKHOLParser}
import at.logic.parsing.language.hlk.ast.LambdaAST
import scala.util.parsing.input.PagedSeqReader
import scala.collection.immutable.PagedSeq
import java.io.FileReader
import at.logic.language.lambda.types.{To, TA}
import at.logic.language.hol._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.base.{Sequent, LKProof, FSequent}
import at.logic.utils.ds.acyclicGraphs.AGraph
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.algorithms.matching.fol.FOLMatchingAlgorithm
import at.logic.algorithms.matching.hol.NaiveIncompleteMatchingAlgorithm
import at.logic.parsing.language.xml.ProofDatabase
import at.logic.algorithms.lk.applySubstitution
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.typedLambdaCalculus.{Abs, App, LambdaExpression, Var}
import at.logic.calculi.lk.equationalRules.{EquationRight2Rule, EquationRight1Rule, EquationLeft2Rule, EquationLeft1Rule}
import at.logic.calculi.lk.equationalRules.EquationVerifier._
import at.logic.calculi.lk.definitionRules.{DefinitionLeftRule, DefinitionRightRule}
import at.logic.language.lambda.BetaReduction._
import scala.annotation.tailrec

abstract class Token
case class TToken(decltype : String, names : List[String], types : TA ) extends Token
case class AToken(rule:String, name : Option[LambdaAST], antecedent: List[LambdaAST], succedent:List[LambdaAST]) extends Token
case class RToken(rule:String, name : Option[LambdaAST],  antecedent: List[LambdaAST],
                     succedent:List[LambdaAST], sub:List[(ast.Var,LambdaAST)]) extends Token


class HybridLatexParserException(m : String, t: Throwable) extends Exception(m, t) {
  def this(m: String) = this(m, null)
}

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

  lazy val rule2 : PackratParser[RToken] = ("\\" ~>
    "(AX|AND[LR]|OR[LR]|IMP[LR]|NEG[LR]|EQ[LR]|WEAK[LR]|CONTR[LR]|CUT|DEF|BETA)".r
    <~ "{") ~ (repsep(formula, ",") <~ "}") ~ ("{" ~> repsep(formula,",") <~ "}") ^^ {
    case name ~ antecedent ~ succedent => RToken(name, None, antecedent, succedent, Nil)
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
    case name  ~ Some(sub)~ arg1 ~ antecedent ~ succedent => println("Parsed sub:"+sub); RToken(name, arg1, antecedent, succedent, sub)
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

/* proof names as stored as formulas now, therefore we extend the proofdatabase */
case class ExtendedProofDatabase(val eproofs : Map[HOLFormula, LKProof])
  extends ProofDatabase(Map(),Nil,Nil,Nil) {
  override val proofs : List[(String,LKProof)] = eproofs.map(x => (x._1.toString, x._2)).toList
  override val Definitions : Map[HOLExpression, HOLExpression] = Map()
  override val axioms : List[FSequent] = Nil
  override val sequentLists : List[(String,List[FSequent])] = Nil
}

trait TokenToLKConverter {
  /* Extracts type declarations from the tokens and creates a function to create atomic terms by name */
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

        throw new HybridLatexParserException("no type declaration for symbol "+s)
    }}
  }


  def printRules(r: List[Token]) : List[FSequent]= {
    val rules = r.filter( _ match { case RToken(_,_,_,_,_) => true; case _ => false}  )
    val naming = createNaming(r)

    var l = List[FSequent]()

    for (RToken(name, argname, antecedent, succedent,_) <- rules) {
      val ant = antecedent.map(x => c(HLKHOLParser.ASTtoHOL( naming  ,x)))
      val suc = succedent.map(x  => c(HLKHOLParser.ASTtoHOL( naming  ,x)))
      val fs = FSequent(ant, suc)
      println(name + ": "+fs)
      l = fs  :: l
    }

    l.reverse
  }

  /* The main entry point to the proof parser. The list of tokens l is taken apart into subproofs (noticable by the
     CONTINUEWITH rule). Then the subproofs are ordered by dependency and constructed in this order*/
  def createLKProof( l : List[Token]) : ExtendedProofDatabase = {
    //seperate rule tokens from type declaration tokens
    val (rtokens, tatokens) = l.partition( _ match {
      case RToken(_,_,_,_,_) =>  true ;
      case _ => false; }
    ).asInstanceOf[(List[RToken], List[Token])] //need to cast because partition returns Tokens
    val (ttokens, atokens) = tatokens.partition( _ match {
        case TToken(_,_,_) =>  true ;
        case t@AToken(_,_,_,_) => println(t); false;
        case t : Token => throw new Exception("Severe error: rule tokens were already filtered out, but rule "+t+" still contained!")
      }
      ).asInstanceOf[(List[TToken], List[AToken])] //need to cast because partition returns Tokens
    val naming = createNaming(ttokens)
    val axioms = createAxioms(naming, atokens)

    //seperate inferences for the different (sub)proofs
    val (last,rm) = rtokens.foldLeft((List[RToken]()), Map[HOLFormula, List[RToken] ]()) ((current, token) => {
      token match {
        case RToken("CONTINUEWITH", Some(name), a, s,_) =>
          //put proof under name into map, continue with empty rulelist
          try {
            val nformula = c(HLKHOLParser.ASTtoHOL(naming, name))
            ( Nil, current._2 + ((nformula,current._1.reverse)) )
          } catch {
            case e:Exception => throw new HybridLatexParserException("Error in parsing CONTINUEWITH{"+name+"}{"+a+"}{"+s"}: "+e.getMessage, e)
          }
        case RToken("CONTINUEWITH", _,_,_,_) =>
          throw new HybridLatexParserException("The CONTINUEWITH statement needs a name giving the argument!")
        case RToken("COMMENT",_,_,_,_) =>
          //filter comments
          current
        case _ =>
          //apend rule to current list
          ( token::current._1, current._2 )
      }
    })

    require(last.isEmpty, "There are some rules left after parsing the list, use CONTINUEFROM to give proof a name! "+last)

    //dependncy analysis
    val dependecies = getDependecyMap(naming, rm)
    //dependecies map (x => println(x._1.toPrettyString+": "+x._2.mkString(",")))
    val ordering : List[HOLFormula] = getOrdering(dependecies)
    println((ordering map (_.toPrettyString)).mkString("Ordering: ",", ",""))

    //proof completion in dependency order
   val proofs =ordering.foldLeft( Map[HOLFormula, LKProof]() )( (proofs_done, f) => {
     println("Processing (sub)proof "+this.f(f))
     val f_proof : LKProof = completeProof(f, proofs_done, naming, rm(f), axioms)
     proofs_done + ((f, f_proof))
    }
   )
   ExtendedProofDatabase(proofs)
  }

  /* Creates the subproof proofname from a list of rules. Uses the naming function to create basic term and
  *  uses the proofs map to look up subproofs referenced by CONTINUEWITH and INSTLEMMA. This means, the calls
  *  to completeProof have to be ordered s.t. dependent proofs are already contained in the map.*/
  def completeProof(proofname : HOLFormula,
                    proofs : Map[HOLFormula, LKProof],
                    naming : String => HOLExpression,
                    rules : List[RToken],
                    axioms : Map[HOLFormula, FSequent]) : LKProof = {
    var proofstack : List[LKProof] = List[LKProof]()
    for ( rt@RToken(name, auxterm, antecedent, succedent,sub) <- rules) {
      println("Processing rule: "+name)
      //println(proofstack.mkString("Proof stack: ",",",""))
      val ant = antecedent.map(x => c(HLKHOLParser.ASTtoHOL( naming  ,x)))
      val suc = succedent.map(x  => c(HLKHOLParser.ASTtoHOL( naming  ,x)))
      val fs = FSequent(ant, suc)
      name match {
        case "AX" =>
          proofstack = Axiom(ant, suc) :: proofstack
         // --- quantifier rules ---
        case "ALLL" =>
          proofstack = handleWeakQuantifier(proofstack, name, fs, auxterm, naming, rt)
        case "EXR" =>
          proofstack = handleWeakQuantifier(proofstack, name, fs, auxterm, naming, rt)
        case "ALLR" =>
          proofstack = handleStrongQuantifier(proofstack, name, fs, auxterm, naming, rt)
        case "EXL" =>
          proofstack = handleStrongQuantifier(proofstack, name, fs, auxterm, naming, rt)
        case "ANDR" =>
          proofstack = handleBinaryLogicalOperator(proofstack, name, fs, auxterm, naming, rt)
        case "ORL" =>
          proofstack = handleBinaryLogicalOperator(proofstack, name, fs, auxterm, naming, rt)
        case "IMPL" =>
          proofstack = handleBinaryLogicalOperator(proofstack, name, fs, auxterm, naming, rt)
        // --- unary rules ---
        case "ORR" =>
          proofstack = handleUnaryLogicalOperator(proofstack, name, fs, auxterm, naming, rt)
        case "ANDL" =>
          proofstack = handleUnaryLogicalOperator(proofstack, name, fs, auxterm, naming, rt)
        case "IMPR" =>
          proofstack = handleUnaryLogicalOperator(proofstack, name, fs, auxterm, naming, rt)
        // --- negation rules ---
        case "NEGL" =>
          proofstack = handleNegation(proofstack, name, fs, auxterm, naming, rt)
        case "NEGR" =>
          proofstack = handleNegation(proofstack, name, fs, auxterm, naming, rt)

        // --- equational rules ---
        case "EQL" =>
          proofstack = handleEquality(proofstack, name, fs, auxterm, naming, rt)
        case "EQR" =>
          proofstack = handleEquality(proofstack, name, fs, auxterm, naming, rt)

        // --- definition rules ---
        case "DEF" =>
          proofstack = handleDefinitions(proofstack, name, fs, auxterm, naming, rt)

        // --- structural rules ---
        case "CONTRL" =>
          proofstack = handleContraction(proofstack, name, fs, auxterm, naming, rt )
        case "CONTRR" =>
          proofstack = handleContraction(proofstack, name, fs, auxterm, naming, rt )
        case "WEAKL" =>
          proofstack = handleWeakening(proofstack, name, fs, auxterm, naming, rt )
        case "WEAKR" =>
          proofstack = handleWeakening(proofstack, name, fs, auxterm, naming, rt )
        case "CUT" =>
          proofstack = handleCut(proofstack, name, fs, auxterm, naming, rt )

        // --- macro rules ---
        case "EQAXIOM" =>
         proofstack = handleEQAxiom(proofstack, name, fs, auxterm, sub, naming, rt, axioms)

        case "INSTAXIOM" =>
          proofstack = handleInstAxiom(proofstack, name, fs, auxterm, sub, naming, rt, axioms)

        case "CONTINUEFROM" =>
          proofstack = handleLink(proofs, proofstack, name, fs, auxterm, naming, rt )
        case "CONTINUEWITH" => ;
        case "COMMENT" => ;
        case _ => throw new HybridLatexParserException("Rule type "+name+" not yet implemented!")
      }
    }

    require(proofstack.nonEmpty,"Error creating proof: Proof stack may not be empty!")
    proofstack.head
  }


  /* Takes care of weak quantifiers. */
  def handleWeakQuantifier(current_proof: List[LKProof], ruletype: String, fs: FSequent, auxterm: Option[LambdaAST], naming: (String) => HOLExpression, rt: RToken): List[LKProof] = {
    require(current_proof.size > 0, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs)
    val oldproof::rest = current_proof

    val (mainsequent, auxsequent, _) = filterContext(oldproof.root.toFSequent, fs)
    require(auxsequent.formulas.size == 1, "Exactly one auxiliary formula in weak quantifier rule required (no autocontraction allowed)! " + auxsequent)
    val (main, aux) = ruletype match {
      case "ALLL" => (mainsequent.antecedent(0), auxsequent.antecedent(0))
      case "EXR"  => (mainsequent.succedent(0), auxsequent.succedent(0))
    }

    def inferTerm(x: Var, f:HOLFormula): HOLExpression = {
      NaiveIncompleteMatchingAlgorithm.holMatch(f, aux)(Nil) match {
        case Some(sub) =>
          val s: HOLExpression = sub.map(x)
          if (auxterm.nonEmpty) {
            //try to use user provided term
            val t: HOLExpression = HLKHOLParser.ASTtoHOL(naming, auxterm.get)
            if (s == t) {
              println("Remark: automatically inferred the auxiliaray term in rule " + rt + ".")
              t
            } else {
              println("Preferring user specified term " + t + " over inferred term " + s + ".")
              t
            }
          } else {
            //no user provided term
            s
          }

        case None =>
          println("Remark: Could not infer substitution term, using user specified one!")
          HLKHOLParser.ASTtoHOL(naming, auxterm.getOrElse(throw new HybridLatexParserException("No substitution term found, please specify! " + rt)))
      }
    }

    main match {
      case AllVar(x, f) =>
        require(ruletype == "ALLL","Main formula "+main+" can not be used in a forall left rule!")
        val term = inferTerm(x,f)
        val rule = ForallLeftRule(oldproof, aux, main, term)
        rule :: rest

      case ExVar(x,f) => inferTerm(x,f)
        require(ruletype == "EXR","Main formula "+main+" can not be used in a exists right rule!")
        val term = inferTerm(x,f)
        val rule = ExistsRightRule(oldproof, aux, main, term)
        rule :: rest
    }
  }

  def handleStrongQuantifier(current_proof: List[LKProof], ruletype:String, fs: FSequent, auxterm: Option[LambdaAST], naming: (String) => HOLExpression, rt: RToken): List[LKProof] = {
    require(current_proof.size > 0, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs)
    val oldproof = current_proof.head
    val (mainsequent, auxsequent, _) = filterContext(oldproof.root.toFSequent, fs)
    require(auxsequent.formulas.size == 1, "Exactly one auxiliary formula in strong quantifier rule required! " + auxsequent)
    val (main, aux) = ruletype match {
      case "EXL" => (mainsequent.antecedent(0), auxsequent.antecedent(0))
      case "ALLR"  => (mainsequent.succedent(0), auxsequent.succedent(0))
    }

    def inferTerm(x: Var, f:HOLFormula): HOLExpression = {
      NaiveIncompleteMatchingAlgorithm.holMatch(f, aux)(Nil) match {
        case Some(sub) =>
          val s: HOLExpression = sub.map(x)
          if (auxterm.nonEmpty) {
            //try to use user provided term
            val t: HOLExpression = HLKHOLParser.ASTtoHOL(naming, auxterm.get)
            if (s == t) {
              println("Remark: automatically inferred the auxiliaray term in rule " + rt + ".")
              require(t.isInstanceOf[HOLVar],  "Strong quantifier rule needs an eigenvariable as argument, but "+t+" is not!")
              t
            } else {
              println("Preferring user specified term " + t + " over inferred term " + s + ".")
              require(t.isInstanceOf[HOLVar],  "Strong quantifier rule needs an eigenvariable as argument, but "+t+" is not!")
              t
            }
          } else {
            //no user provided term
            require(s.isInstanceOf[HOLVar],  "Strong quantifier rule needs an eigenvariable as argument, but "+s+" is not!")
            s
          }

        case None =>
          //automatic mode failed
          println("Remark: Could not infer substitution term, using user specified one!")
          val t = HLKHOLParser.ASTtoHOL(naming, auxterm.getOrElse(throw new HybridLatexParserException("No substitution term found, please specify! " + rt)))
          require(t.isInstanceOf[Var],  "Strong quantifier rule needs an eigenvariable as argument, but "+t+" is not!")
          t
      }
    }

    main match {
      case AllVar(x, f) =>
        require(ruletype == "ALLR","Main formula "+main+" can not be used in a forall right rule!")
        val term : HOLVar = inferTerm(x,f).asInstanceOf[HOLVar]
        val rule = ForallRightRule(oldproof, aux, main, term)
        rule :: current_proof.tail

      case ExVar(x,f) => inferTerm(x,f)
        require(ruletype == "EXL","Main formula "+main+" can not be used in a exists left rule!")
        val term : HOLVar = inferTerm(x,f).asInstanceOf[HOLVar]
        val rule = ExistsLeftRule(oldproof, aux, main, term)
        rule :: current_proof.tail
    }
  }

  def handleBinaryLogicalOperator(current_proof: List[LKProof], ruletype:String, fs: FSequent, auxterm: Option[LambdaAST], naming: (String) => HOLExpression, rt: RToken): List[LKProof] = {
    require(current_proof.size > 1, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs)
    val rightproof::leftproof::stack = current_proof

    val (mainsequent, auxsequent, context) = filterContext(leftproof.root.toFSequent, rightproof.root.toFSequent, fs)

    try {
    ruletype match {
      case "ANDR" =>
        mainsequent.succedent(0) match {
          case And(l,r) =>
            require(auxsequent.succedent.contains(l), "Left branch formula "+l+" not found in auxiliary formulas"+f(auxsequent))
            require(auxsequent.succedent.contains(r), "Right branch formula "+r+" not found in auxiliary formulas!"+f(auxsequent))
            require(leftproof.root.toFSequent.succedent.contains(l), "Left branch formula "+l+" not found in auxiliary formulas "+leftproof.root)
            require(rightproof.root.toFSequent.succedent.contains(r), "Right branch formula "+r+" not found in auxiliary formulas!"+rightproof.root)
            val inf = AndRightRule(leftproof, rightproof, l,r)
            val contr = contract(inf, fs)
            contr :: stack
          case _ => throw new HybridLatexParserException("Main formula of a conjunction right rule must have conjuntion as outermost operator!")
        }

      case "ORL"  =>
        mainsequent.antecedent(0) match {
          case Or(l,r) =>
            require(auxsequent.antecedent.contains(l), "Left branch formula "+l+" not found in auxiliary formulas "+f(auxsequent))
            require(auxsequent.antecedent.contains(r), "Right branch formula "+r+" not found in auxiliary formulas!"+f(auxsequent))
            require(leftproof.root.toFSequent.antecedent.contains(l), "Left branch formula "+l+" not found in auxiliary formulas "+leftproof.root)
            require(rightproof.root.toFSequent.antecedent.contains(r), "Right branch formula "+r+" not found in auxiliary formulas!"+rightproof.root)
            val inf = OrLeftRule(leftproof, rightproof, l,r)
            val contr = contract(inf, fs)
            contr :: stack
          case _ => throw new HybridLatexParserException("Main formula of a disjunction left rule must have disjunction as outermost operator!")
        }

      case "IMPL" =>
        mainsequent.antecedent(0) match {
          case Imp(l,r) =>
            require(auxsequent.succedent.contains(l), "Left branch formula "+l+" not found in auxiliary formulas "+f(auxsequent))
            require(auxsequent.antecedent.contains(r), "Right branch formula "+r+" not found in auxiliary formulas!"+f(auxsequent))
            require(leftproof.root.toFSequent.succedent.contains(l), "Left branch formula "+l+" not found in auxiliary formulas "+leftproof.root)
            require(rightproof.root.toFSequent.antecedent.contains(r), "Right branch formula "+r+" not found in auxiliary formulas!"+rightproof.root)
            val inf = ImpLeftRule(leftproof, rightproof, l,r)
            val contr = contract(inf, fs)
            contr :: stack
          case _ => throw new HybridLatexParserException("Main formula of a implication left rule must have implication as outermost operator!")
        }
    }
    } catch {
      case e: Exception => throw new HybridLatexParserException("Error in handling binary rule with end-sequent: "+f(fs)+"\nProblem: "+e.getMessage, e)
    }
  }

  def handleUnaryLogicalOperator(current_proof: List[LKProof], ruletype:String, fs: FSequent, auxterm: Option[LambdaAST], naming: (String) => HOLExpression, rt: RToken): List[LKProof] = {
    require(current_proof.size > 0, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs)
    val top::stack = current_proof

    val (mainsequent, auxsequent, context) = filterContext(top.root.toFSequent, fs)

    ruletype match {
      case "ORR" =>
        mainsequent.succedent(0) match {
          case Or(l,r) =>
            require(top.root.toFSequent.succedent.contains(l)|top.root.toFSequent.succedent.contains(r), "Neither "+l+" nor "+r+" found in auxiliary formulas"+f(auxsequent))

            //try out which of the 3 variants of the rule it is
            val inf1 = try {
              val inf = OrRight1Rule(top, l,r)
              val contr = contract(inf, fs)
              Some(contr)
            } catch {
              case e:Exception => None
            }

            val inf2 = try {
              val inf = OrRight2Rule(top, l,r)
              val contr = contract(inf, fs)
              Some(contr)
            } catch {
              case e:Exception => None
            }

            val inf3 = try {
              val inf = OrRight1Rule(top, l,r)
              val inf_ = OrRight2Rule(inf, l,r)
              val contr = contract(inf_, fs)
              Some(contr)
            } catch {
              case e:Exception => None
            }

            val worked = List(inf1,inf2,inf3).filter( _.isDefined )
            require(worked.nonEmpty, "Could not infer or right rule "+fs+" from "+top.root)

            worked(0).get :: stack
          case _ => throw new HybridLatexParserException("Main formula of a disjunction right rule must have conjuntion as outermost operator!")
        }

      case "ANDL"  =>
        mainsequent.antecedent(0) match {
          case And(l,r) =>
            require(top.root.toFSequent.antecedent.contains(l)|top.root.toFSequent.antecedent.contains(r), "Neither "+l+" nor "+r+" found in auxiliary formulas"+f(auxsequent))

            //try out which of the 3 variants of the rule it is
            val inf1 = try {
              val inf = AndLeft1Rule(top, l,r)
              val contr = contract(inf, fs)
              Some(contr)
            } catch {
              case e:Exception => None
            }

            val inf2 = try {
              val inf = AndLeft2Rule(top, l,r)
              val contr = contract(inf, fs)
              Some(contr)
            } catch {
              case e:Exception => None
            }

            val inf3 = try {
              val inf = AndLeft1Rule(top, l,r)
              val inf_ = AndLeft2Rule(inf, l,r)
              val contr = contract(inf_, fs)
              Some(contr)
            } catch {
              case e:Exception => None
            }

            val worked = List(inf1,inf2,inf3).filter( _.isDefined )
            require(worked.nonEmpty, "Could not infer or right rule "+fs+" from "+top.root)

            worked(0).get :: stack
          case _ => throw new HybridLatexParserException("Main formula of a conjunction left rule must have disjunction as outermost operator!")
        }

      case "IMPR" =>
        mainsequent.succedent(0) match {
          case Imp(l,r) =>
            require(auxsequent.antecedent.contains(l), "Left branch formula "+l+" not found in auxiliary formulas "+f(auxsequent))
            require(auxsequent.succedent.contains(r), "Right branch formula "+r+" not found in auxiliary formulas!"+f(auxsequent))
            require(top.root.toFSequent.antecedent.contains(l), "Left branch formula "+l+" not found in auxiliary formulas "+top.root)
            require(top.root.toFSequent.succedent.contains(r), "Right branch formula "+r+" not found in auxiliary formulas!"+top.root)
            val inf = ImpRightRule(top, l,r)
            val contr = contract(inf, fs)
            contr :: stack
          case _ => throw new HybridLatexParserException("Main formula of a implication right rule must have implication as outermost operator!")
        }
    }
  }

  def handleNegation(current_proof: List[LKProof], ruletype:String, fs: FSequent, auxterm: Option[LambdaAST], naming: (String) => HOLExpression, rt: RToken): List[LKProof] = {
    require(current_proof.size > 0, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs)
    val top::stack = current_proof
    val (main, aux, context) = filterContext(top.root.toFSequent, fs)

    val left = main.antecedent.foldLeft(top)((intermediate, f) => {
      f match {
        case Neg(g) =>
          NegLeftRule(intermediate,g)
        case _ =>
          throw new HybridLatexParserException("Trying to apply the negation rule on formula "+f+" without negation as outermost symbol on "+top.root+" to get "+fs)
      }
     }
    )
    val right = main.succedent.foldLeft(left)((intermediate, f) => {
      f match {
        case Neg(g) =>
          NegRightRule(intermediate,g)
        case _ =>
          throw new HybridLatexParserException("Trying to apply the negation rule on formula "+f+" without negation as outermost symbol on "+top.root+" to get "+fs)
      }
    }
    )

    val contr = contract(right, fs)

    require(contr.root.toFSequent multiSetEquals fs,"Could not create target sequent "+fs+" by a series of negations from "+top.root+" but got "+contr.root+" instead!" )
    contr :: stack
  }

  def handleEquality(current_proof: List[LKProof], ruletype:String, fs: FSequent, auxterm: Option[LambdaAST], naming: (String) => HOLExpression, rt: RToken): List[LKProof] = {
    require(current_proof.size > 1, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs)
    val rightproof::leftproof::stack = current_proof

    //In the case the main formula is the same as an auxiliariy formula, filterContext cannot infer the main formula
    //we doe this now by hand
    def eqfilter(x:HOLFormula) : Boolean = x match { case Equation(s,t) => true; case _ => false }
    def canReplace(s:HOLExpression, t:HOLExpression, exp1 : HOLExpression, exp2:HOLExpression) : Boolean = {
      (checkReplacement(s,t,exp1,exp2), checkReplacement(t,s,exp1,exp2)) match {
        case (EqualModuloEquality(_), _) => true
        case (_, EqualModuloEquality(_)) => true
        case _ => false
      }
    }

    val lefteqs = leftproof.root.toFSequent.succedent.filter( eqfilter )
    ruletype match {
      case "EQL" =>
        //we find all candidates, i.e. equations e: s=t in the left parent and pair it with possible formulas f
        // from the right parent together with possible main formulas in the conclusion s.t. f[s] = main[t] or
        // f[t] = main[s]
        val righteqsante = rightproof.root.toFSequent.antecedent
        val candidates = for( e@Equation(s,t) <- lefteqs;
                              f <- righteqsante;
                              main <- fs.antecedent;
                              if canReplace(s,t,f,main)  )
        yield { (s,t,e,f,main)}

        require(candidates.nonEmpty,"For an eq:l rule, could not find a possible replacement of an equation from "
          +lefteqs.map(this.f(_)).mkString("(",",",")")+" in "+fs.antecedent.map(this.f(_)).mkString("(",",",")")  )

        //now we try to create an inference from each candidate
        val inferences : Seq[LKProof] = candidates.flatMap( args => {
          val (s,t,eq,f,main) = args
          val l1 = {
            //we check if we can paramodulate s=t ...
            checkReplacement(s, t, f, main) match {
              case EqualModuloEquality(_) =>
                val rule = EquationLeft1Rule(leftproof, rightproof, eq, f, main)
                try {
                  contract(rule,fs)::Nil
                } catch {
                  case e:Exception => Nil
                }
              case _ =>
                Nil
            }
          }
            val l2 = {
              //if not we try t=s....
                  checkReplacement(t, s, f, main) match {
                    case EqualModuloEquality(_) =>
                      val rule = EquationLeft2Rule(leftproof, rightproof, eq, f, main)
                      try {
                        contract(rule,fs)::Nil
                      } catch {
                        case e:Exception => Nil
                      }
                    case _ =>
                      Nil
                  }
                }
            l1 ++ l2
        })

        require(inferences.nonEmpty, "Could not infer an eq:l rule from left parent "+this.f(leftproof.root)
          +" and "+this.f(rightproof.root)+" to infer "+this.f(fs))
        if (inferences.size > 1)
          println("WARNING: Inference to create eq:l rule is not uniquely specified from left parent "
            +leftproof.root+" and "+rightproof.root+" to infer "+fs)

        inferences(0)::stack


      case "EQR" =>
        //we find all candidates, i.e. equations e: s=t in the left parent and pair it with possible formulas f
        // from the right parent together with possible main formulas in the conclusion
        val righteqssucc = rightproof.root.toFSequent.succedent
        val candidates = for( e@Equation(s,t) <- lefteqs;
                              f <- righteqssucc;
                              main <- fs.succedent;
                              if canReplace(s,t,f,main)  )
        yield { (s,t,e,f,main)}

        require(candidates.nonEmpty,"For an eq:r rule, could not find a possible replacement of an equation from "
          +lefteqs.map(this.f(_)).mkString("(",",",")")+" in "+fs.succedent.map(this.f(_)).mkString("(",",",")") )

        //now we try to create an inference from each candidate
        val inferences : Seq[LKProof] = candidates.flatMap( args => {
          val (s,t,eq,f,main) = args

          val l1 = {
            print("Trying"+this.f(s)+"="+this.f(t)+" in "+this.f(main))
            //we check if we can paramodulate s=t ...
            checkReplacement(s, t, f, main) match {
              case EqualModuloEquality(_) =>
                println("found!")
                val rule = EquationRight1Rule(leftproof, rightproof, eq, f, main)
                try {
                  contract(rule,fs)::Nil
                } catch {
                  case e:Exception => Nil
                }
              case _ =>
                Nil
            }
          }

          val l2 = {
            //if not, we try t=s....
            print("Trying"+this.f(t)+"="+this.f(s)+" in "+this.f(main))
            checkReplacement(t, s, f, main) match {
              case EqualModuloEquality(_) =>
                println("found!")
                val rule = EquationRight2Rule(leftproof, rightproof, eq, f, main)
                try {
                  contract(rule,fs)::Nil
                } catch {
                  case e:Exception => Nil
                }

              case _ =>
                Nil
            }
          }

          l1++l2
        })

        require(inferences.nonEmpty, "Could not infer an eq:r rule from left parent "+this.f(leftproof.root)
          +" and "+this.f(rightproof.root)+" to infer "+this.f(fs))
        if (inferences.size > 1)
          println("WARNING: Inference to create eq:r rule is not uniquely specified from left parent "
            +leftproof.root+" and "+rightproof.root+" to infer "+fs)

        inferences(0)::stack

      case _ => throw new Exception("Epected equational rule but got rule name: "+ruletype)
    }
  }

  //TODO: integrate which definitions were used into the proof
  def handleDefinitions(current_proof: List[LKProof], ruletype:String, fs: FSequent, auxterm: Option[LambdaAST], naming: (String) => HOLExpression, rt: RToken): List[LKProof] = {
    require(current_proof.size > 0, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs)
    val parent::stack = current_proof
    val (mainsequent, auxsequent, context) = filterContext(parent.root.toFSequent, fs)
    require( auxsequent.formulas.size == 1, "Definition rules expect exactly one auxiliary formula, not "+f(auxsequent) )
    require( (auxsequent.antecedent.size == mainsequent.antecedent.size) &&
             (auxsequent.succedent.size == mainsequent.succedent.size), "The definition needs to be on the same side!")

    (auxsequent, mainsequent) match {
      case (FSequent(Nil, List(aux)), FSequent(Nil, List(main))) =>
        val rule = DefinitionRightRule(parent, aux, main)
        rule ::stack
      case (FSequent(List(aux),Nil), FSequent(List(main),Nil)) =>
        val rule = DefinitionLeftRule(parent, aux, main)
        rule ::stack
      case _ =>
        throw new HybridLatexParserException("Error in creation of definition rule, can not infer "+f(mainsequent)+" from "+f(auxsequent))
    }
  }


   /*   =================== STRUCTURAL RULES =============================    */
    def handleContraction(current_proof: List[LKProof], ruletype:String, fs: FSequent, auxterm: Option[LambdaAST], naming: (String) => HOLExpression, rt: RToken): List[LKProof] = {
    require(current_proof.size > 0, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs)
    val parentproof::stack = current_proof
    val inf = contract(parentproof, fs)
    inf :: stack
  }

  def handleWeakening(current_proof: List[LKProof], ruletype:String, fs: FSequent, auxterm: Option[LambdaAST], naming: (String) => HOLExpression, rt: RToken): List[LKProof] = {
    require(current_proof.size > 0, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs)
    val parentproof::stack = current_proof
    val inf = weaken(parentproof, fs)
    inf :: stack
  }

  def handleCut(current_proof: List[LKProof], ruletype:String, fs: FSequent, auxterm: Option[LambdaAST], naming: (String) => HOLExpression, rt: RToken): List[LKProof] = {
    require(current_proof.size > 1, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs)
    val rightproof::leftproof::stack = current_proof

    val auxsequent = (leftproof.root.toFSequent compose rightproof.root.toFSequent) diff fs
    require(auxsequent.antecedent.size == 1 && auxsequent.succedent.size == 1, "Need exactly one formula in the antecedent and in the succedent of the parents!"+f(auxsequent))
    require(auxsequent.antecedent(0) == auxsequent.succedent(0), "Cut formula right ("+auxsequent.antecedent(0)+") is not equal to cut formula left ("+auxsequent.succedent(0)+")")
    val cutformula = auxsequent.antecedent(0)
    require(leftproof.root.toFSequent.succedent contains cutformula, "Cut formula "+cutformula+" must occur in succedent of "+leftproof.root)
    require(rightproof.root.toFSequent.antecedent contains cutformula, "Cut formula "+cutformula+" must occur in antecedent of "+rightproof.root)
    val inf = CutRule(leftproof, rightproof, cutformula)
    require(inf.root.toFSequent multiSetEquals fs, "Inferred sequent "+inf.root+" is what was not expected: "+fs)
    inf :: stack
  }

  def handleLink(proofs : Map[HOLFormula, LKProof], current_proof: List[LKProof],
                 ruletype:String, fs: FSequent, auxterm: Option[LambdaAST],
                 naming: (String) => HOLExpression, rt: RToken): List[LKProof] = {
    require(auxterm.isDefined, "Can not refer to a subproof(CONTINUEFROM): Need a proof name to link to!")
    val link = HLKHOLParser.ASTtoHOL(naming, auxterm.get)
    val ps : List[LKProof] = proofs.toList.flatMap( x => {
      NaiveIncompleteMatchingAlgorithm.holMatch(x._1,link)(Nil) match {
        case None => Nil
        case Some(sub) =>
          applySubstitution(x._2, sub)._1 :: Nil
      }
    }
    )

    require(ps.nonEmpty, "None of the proofs in "+proofs.keys.mkString("(",",",")")+" matches proof link "+link  )
    require(ps(0).root.toFSequent.multiSetEquals(fs), "LINK to "+this.f(link)+" must give "+this.f(fs)+" but gives "+this.f(ps(0).root))

    ps(0) :: current_proof

  }


  def createSubstitution(naming : String => HOLExpression, astlist : List[(ast.Var, LambdaAST)]) : Substitution[HOLExpression] = {
    val terms : List[(Var, HOLExpression)] = astlist.foldLeft(List[(Var, HOLExpression)]())((list, p) => {
      (HLKHOLParser.ASTtoHOL(naming, p._1).asInstanceOf[Var], HLKHOLParser.ASTtoHOL(naming, p._2)) :: list
    })
    Substitution[HOLExpression](terms.reverse)
  }

  /* =============== Macro Rules ============================ */

  val axioms_prove_sequent = FSequent(List(Atom(HOLConst(ConstantStringSymbol("AX"), To()), Nil)), Nil)
  def normalize(exp:HOLExpression) = betaNormalize(exp)(StrategyOuterInner.Outermost).asInstanceOf[HOLExpression]

  def handleEQAxiom(current_proof: List[LKProof], ruletype: String, fs: FSequent, auxterm: Option[LambdaAST],
                    subterm : List[(ast.Var,LambdaAST)], naming: (String) => HOLExpression,
                    rt: RToken, axioms : Map[HOLFormula, FSequent]): List[LKProof] = {
    require(current_proof.size > 0, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs)
    val oldproof::rest = current_proof
    require(auxterm.isDefined, "Error creating an equational axiom rule: Need instantiation annotation!")
    val auxf = c(HLKHOLParser.ASTtoHOLnormalized(naming, auxterm.get))

    val sub = createSubstitution(naming, subterm)

    val axs : List[FSequent] = axioms.toList.map(_._2)
    val candidates = axs.flatMap( s => {
      val FSequent(Nil, List(ax1)) = s
      val (_,ax2) = stripUniversalQuantifiers(ax1)
      val ax=  normalize(sub(ax2))
      //println("Trying:"+this.f(ax))
      NaiveIncompleteMatchingAlgorithm.holMatch(ax, auxf)(Nil) match {
        case Some(sub) => (ax,sub)::Nil
        case None => Nil
      }
    })

    require(candidates.size > 0, "Could not find equational axiom for "+f(auxf))
    if(candidates.size > 1)
      println("Warning: Axiom not uniquely specified, possible candidates: "+candidates.map(x=> this.f(x._1)+" "+x._2).mkString(","))
    val candidate = candidates(0)

    //val vars = candidate._1.freeVariables.toList.sorted
    //vars.foldLeft(Axiom(auxf,auxf))

    //TODO:generate correct axiomatization, at the moment we use AX :- instance for everything
    val axfs = axioms_prove_sequent compose FSequent(Nil, List(auxf))
    val axrule : LKProof = Axiom(axfs.antecedent, axfs.succedent )
    val Equation(s,t) = auxf

    val auxsequent = oldproof.root.toFSequent diff fs
    val mainsequent = fs diff (oldproof.root.toFSequent compose axioms_prove_sequent)
    require(mainsequent.formulas.size == 1, "Exactly one main formula required, not "+f(mainsequent))
    require(auxsequent.formulas.size == 1, "Excatly one auxiliary formula needed in parent, not "+f(auxsequent))
    val newproof = auxsequent match {
      case FSequent(Nil, List(f)) =>
        require(mainsequent.antecedent.size == 0 && mainsequent.succedent.size == 1,
          "Auxformula and main formula in eqaxiom rule need to be on the same side of the sequent, not "
            +this.f(mainsequent)+" and "+this.f(auxsequent))
        val FSequent(Nil,List(main)) = mainsequent
        (checkReplacement(s,t,f,main), checkReplacement(t,s,f,main)) match {
          case (EqualModuloEquality(_), _) =>
            EquationRight1Rule(axrule, oldproof, auxf, f, main)
          case (_,EqualModuloEquality(_)) =>
            EquationRight2Rule(axrule, oldproof, auxf, f, main)
          case _ => throw new Exception("Could not find replacement of equational axiom "+this.f(auxf)+" in "+this.f(main))
        }

      case FSequent(List(f), Nil) =>
        require(mainsequent.antecedent.size == 1 && mainsequent.succedent.size == 0,
          "Auxformula and main formula in eqaxiom rule need to be on the same side of the sequent, not "
            +this.f(mainsequent)+" and "+this.f(auxsequent))
        val FSequent(List(main), Nil) = mainsequent
        (checkReplacement(s,t,f,main), checkReplacement(t,s,f,main)) match {
          case (EqualModuloEquality(_), _) =>
            EquationLeft1Rule(axrule, oldproof, auxf, f, main)
          case (_,EqualModuloEquality(_)) =>
            EquationLeft2Rule(axrule, oldproof, auxf, f, main)
          case _ => throw new Exception("Could not find replacement of equational axiom "+auxf+" in "+main)
        }
    }

    val cproof = contract(newproof, fs)

    cproof::rest
  }


  def handleInstAxiom(current_proof: List[LKProof], ruletype: String, fs: FSequent, auxterm: Option[LambdaAST], subterm : List[(ast.Var,LambdaAST)],
                    naming: (String) => HOLExpression, rt: RToken, axioms : Map[HOLFormula, FSequent]): List[LKProof] = {
    require(current_proof.size > 0, "Imbalanced proof tree in application of " + ruletype + " with es: " + fs)
    val oldproof::rest = current_proof
    //require(auxterm.isDefined, "Error creating an stantiate axiom rule: Need instantiation annotation!")
    //val auxf = c(HLKHOLParser.ASTtoHOL(naming, auxterm.get))
    val auxsequent = oldproof.root.toFSequent diff fs
    val mainsequent = fs diff (oldproof.root.toFSequent compose axioms_prove_sequent)

    require(mainsequent.formulas.size == 0,
      "The instantiate axiom rule should not have a main formula, we got: "+f(mainsequent))
    require(auxsequent.antecedent.size == 1 && auxsequent.succedent.size == 0,
      "Auxformula formula in inst axiom rule need to be on the lh side of the sequent, not "+f(auxsequent))

    val FSequent(List(auxf_), Nil) = auxsequent
    val auxf = c(betaNormalize(auxf_)(StrategyOuterInner.Outermost).asInstanceOf[HOLExpression])

    println("auxf="+this.f(auxf))

    val sub = createSubstitution(naming, subterm)
    println(sub)

    val axs : List[FSequent] = axioms.toList.map(_._2)
    val candidates = axs.flatMap( s => {
      val FSequent(Nil, List(ax1)) = s
      val (_,ax2) = stripUniversalQuantifiers(ax1)
      val ax=  betaNormalize(sub(ax2))(StrategyOuterInner.Outermost).asInstanceOf[HOLExpression]
      //println("Trying: "+ this.f(ax))
      NaiveIncompleteMatchingAlgorithm.holMatch(ax, auxf)(Nil) match {
        case Some(sub) => (ax,sub)::Nil
        case None => Nil
      }
    })

    require(candidates.size > 0, "Could not find instance axiom for "+f(auxf))
    if(candidates.size > 1)
      println("Warning: Axiom not uniquely specified, possible candidates: "+candidates.map(x=> this.f(x._1)+" "+x._2).mkString(","))
    val candidate = candidates(0)

    //val vars = candidate._1.freeVariables.toList.sorted
    //vars.foldLeft(Axiom(auxf,auxf))

    //TODO:generate correct axiomatization, at the moment we use AX :- instance for everything
    val axfs = axioms_prove_sequent compose FSequent(Nil, List(auxf))
    val axrule : LKProof = Axiom(axfs.antecedent, axfs.succedent )

    require(auxsequent.formulas.size == 1, "Excatly one auxiliary formula needed in parent, not "+f(auxsequent))
    val newproof = auxsequent match {
      case FSequent(List(f), Nil) =>
        contract(CutRule(axrule, oldproof, auxf), fs)
    }

    newproof::rest
  }


  //TODO: there is definitely a copy of contract somewhere. Find it and eliminate the redundancy.
  /* Apply contraction rules to a proof until a given end-sequent is obtained.
    Throws an exception if this is impossible. */
  def contract(proof : LKProof, towhat : FSequent) : LKProof = {
    val context = proof.root.toFSequent diff towhat
    val leftcontr : LKProof = context.antecedent.foldLeft(proof)((intermediate, f) =>
      try {
        ContractionLeftRule(intermediate, f)
      } catch {
        case e : Exception =>
          throw new HybridLatexParserException("Could not contract "+f+" in "+proof.root+"!",e)
      }
    )
    val rightcontr : LKProof = context.succedent.foldLeft(leftcontr)((intermediate, f) =>
      try {
        ContractionRightRule(intermediate, f)
      } catch {
        case e : Exception =>
          throw new HybridLatexParserException("Could not contract "+f+" in "+proof.root+"!",e)
      }
    )

    require(rightcontr.root.toFSequent.multiSetEquals( towhat ), "Context of contraction errenous: "+proof.root+" does not contract to "+rightcontr.root)

    rightcontr
  }

  //TODO: there is definitely a copy of weaken somewhere. Find it and eliminate the redundancy.
  /* Apply weakening rules to a proof until a given end-sequent is obtained.
    Throws an exception if this is impossible. */
  def weaken(proof : LKProof, towhat : FSequent) : LKProof = {
    val context = towhat diff proof.root.toFSequent
    val leftcontr : LKProof = context.antecedent.foldLeft(proof)((intermediate, f) =>
      try {
        WeakeningLeftRule(intermediate, f)
      } catch {
        case e : Exception =>
          throw new HybridLatexParserException("Could not contract "+f+" in "+proof.root+"!",e)
      }
    )
    val rightcontr : LKProof = context.succedent.foldLeft(leftcontr)((intermediate, f) =>
      try {
        WeakeningRightRule(intermediate, f)
      } catch {
        case e : Exception =>
          throw new HybridLatexParserException("Could not contract "+f+" in "+proof.root+"!",e)
      }
    )

    require(rightcontr.root.toFSequent.multiSetEquals( towhat ), "Context of weakening errenous: "+proof.root+" does not contract to "+rightcontr.root)

    rightcontr
  }

  /* given a map of elements to lists of dependant elements (e.g. a node's children in a graph), calculate a list l where
   * for every element a occurring before an element b in l we know that a does not depend on b.
   * Throws an exception, if the dependency graph contains cycles. */
  def getOrdering[T](pm : Map[T, List[T]]) : List[T] = {
    val (leaves, nonleaves) = pm.partition( el => el._2.isEmpty )
    require(leaves.nonEmpty, "Circular dependency detected: "+pm)
    val leaflist = leaves.keySet.toList
    if (nonleaves.isEmpty) {
      leaflist
    } else {
      //remove leaves from the graph
      val rest = nonleaves map ( el => (el._1, el._2 filterNot(leaflist contains _)))
      leaflist ++ getOrdering(rest)
    }
  }

  /* Extracts a map of dependencies between subproofs from a mapping of proof names to the token lists representing them. */
  def getDependecyMap(naming : String => HOLExpression,pm : Map[HOLFormula, List[RToken]]) : Map[HOLFormula,List[HOLFormula]] = {
    val proofnames = pm.keySet.toList
    // only keep continuefrom tokens in the lists, map to the formulas in
    // the proofnames against which the dependencies matches
    pm.map( element =>
      (element._1, element._2.flatMap( _ match {
        case RToken("CONTINUEFROM",Some(f),_,_,_) =>
          //find the matching proofs
          proofnames.filter( p =>
            NaiveIncompleteMatchingAlgorithm.holMatch(p, c(HLKHOLParser.ASTtoHOL(naming, f)))(Nil).isDefined
          ) match {
            //and check if the dependency is ok
            case Nil =>
              throw new HybridLatexParserException("Could not find a matching dependency for proof "+f
                +" in: "+proofnames.mkString(","))
            case l@List(d) =>
              l
            case _ =>
              throw new HybridLatexParserException("Found more than one matching dependency for proof "+f
                +" in: "+proofnames.mkString(",")+" but proof links need to be unique!")
          }

        case RToken("INSTLEMMA",Some(f),_,_,_) =>
          //find the matching proofs
          proofnames.filter( p =>
            NaiveIncompleteMatchingAlgorithm.holMatch(p, c(HLKHOLParser.ASTtoHOL(naming, f)))(Nil).isDefined
          ) match {
            //and check if the dependency is ok
            case Nil =>
              throw new HybridLatexParserException("Could not find a matching dependency for proof "+f
                +" in: "+proofnames.mkString(","))
            case l@List(d) =>
              l
            case _ =>
              throw new HybridLatexParserException("Found more than one matching dependency for proof "+f
                +" in: "+proofnames.mkString(",")+" but proof links need to be unique!")
          }

        case RToken("CONTINUEFROM",_,_,_,_) =>
          throw new HybridLatexParserException("The CONTINUEFROM statement needs a proof as an argument!")
        case RToken("INSTLEMMA",_,_,_,_) =>
          throw new HybridLatexParserException("The INSTLEMMA statement needs a proof as an argument!")
        case _ => Nil
      }))
    )
  }


  /* remove common context from sequent (fs_old) and inferred sequent (fs_new).
   * return a triple: (sequent with main formula,
   *                   sequent with auxiliary and uncontracted formulas,
   *                   context sequent) */
  def filterContext(fs_old : FSequent, fs_new : FSequent) : (FSequent, FSequent,FSequent) = {
    val ndiff = fs_new diff fs_old
    val odiff = fs_old diff fs_new

    val csequent = fs_new diff ndiff

    try {
      require(ndiff.formulas.length == 1, "We want exactly one primary formula, not: "+f(ndiff)+ " in "+f(fs_new))
      require(odiff.formulas.length > 0, "We want at least one auxiliary formula, not: "+f(odiff)+ " in "+f(fs_old))
    } catch {
      case e:Exception => throw new HybridLatexParserException(e.getMessage,e)
    }
    (ndiff, odiff, csequent)
  }

  /* creates a map from axiom names to the corresponding fsequents from a list of axiom tokens,
   * supposed to be passed on to EQAXIOM and INSTAXIOM rules */
  def createAxioms(naming : String => HOLExpression,l : List[AToken]) : Map[HOLFormula, FSequent] = {
    l.filter(_.rule == "AXIOMDEC" ).foldLeft(Map[HOLFormula, FSequent]())( (map, token) => {
      val AToken(rulename, aname, antecedent, succedent ) = token
      require(aname.nonEmpty, "Axiom declaration "+token+" needs a name!")
        val aformula : HOLFormula = c(HLKHOLParser.ASTtoHOL(naming, aname.get))
        val ant = antecedent.map(x => c(HLKHOLParser.ASTtoHOL( naming  ,x)))
        val suc = succedent.map(x  => c(HLKHOLParser.ASTtoHOL( naming  ,x)))
        val fs = FSequent(ant, suc)
        require(ant.isEmpty && suc.size == 1, "Axiom declarations need to be one positive formula, not "+fs)
        map + ((aformula, fs))
    })
  }

  /* remove common context from 2 sequents (fs_old1, fs_old2) and inferred sequent (fs_new).
   * return a triple: (sequent with main formula,
   *                   sequent with auxiliary and uncontracted formulas,
   *                   context sequent) */
  def filterContext(fs_old1 : FSequent, fs_old2 : FSequent, fs_new : FSequent) : (FSequent, FSequent, FSequent) =
    filterContext(fs_old1 compose fs_old2, fs_new)

  /* removes univarsal quantifiers from f and returns the list of quantified variables together
   * with the stripped formula */
  def stripUniversalQuantifiers(f:HOLFormula) : (List[HOLVar], HOLFormula)= stripUniversalQuantifiers(f, Nil)
  @tailrec
  private def stripUniversalQuantifiers(f:HOLFormula, acc : List[HOLVar]) : (List[HOLVar], HOLFormula) = f match {
    case AllVar(x,f_) => stripUniversalQuantifiers(f_, x.asInstanceOf[HOLVar]::acc)
    case _ => (acc.reverse, f)
  }

  /* Checked cast of HOLExpression to HOLFormula which gives a nicer error message */
  private def c(e:HOLExpression) : HOLFormula =
    if (e.isInstanceOf[HOLFormula]) e.asInstanceOf[HOLFormula] else
      throw new Exception("Could not convert "+e+" to a HOL Formula!")

  /* formats a sequent */
  private def f(fs:FSequent) : String = {
    " "+(fs.antecedent.map(HybridLatexExporter.getFormulaString(_)).mkString(", ")) + " :- " +
    (fs.succedent.map(HybridLatexExporter.getFormulaString(_)).mkString(", "))+" "
  }

  private def f(fs:Sequent) : String = f(fs.toFSequent)
  private def f(e:HOLExpression) : String = " "+HybridLatexExporter.getFormulaString(e)+" "

}
