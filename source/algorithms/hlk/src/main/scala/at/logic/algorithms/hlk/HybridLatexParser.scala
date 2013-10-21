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
import at.logic.language.lambda.typedLambdaCalculus.Var

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

  /* The main entry point to the proof parser. The list of tokens l is taken apart into subproofs (noticable by the
     CONTINUEWITH rule). Then the subproofs are ordered by dependency and constructed in this order*/
  def createLKProof( l : List[Token]) : Map[HOLFormula, LKProof] = {
    //seperate rule tokens from type declaration tokens
    val (rtokens, ttokens) = l.partition( _ match {
      case RToken(_,_,_,_) =>  true ;
      case TToken(_,_,_) => false; }
    ).asInstanceOf[(List[RToken], List[TToken])] //need to cast because partition returns Tokens
    val naming = createNaming(ttokens)

    //seperate inferences for the different (sub)proofs
    val (last,rm) = rtokens.foldLeft((List[RToken]()), Map[HOLFormula, List[RToken] ]()) ((current, token) => {
      token match {
        case RToken("CONTINUEWITH", Some(name), a, s) =>
          //put proof under name into map, continue with empty rulelist
          try {
            val nformula = c(HLKHOLParser.ASTtoHOL(naming, name))
            ( Nil, current._2 + ((nformula,current._1.reverse)) )
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

    //dependncy analysis
    val dependecies = getDependecyMap(naming, rm)
    //dependecies map (x => println(x._1.toPrettyString+": "+x._2.mkString(",")))
    val ordering : List[HOLFormula] = getOrdering(dependecies)
    println((ordering map (_.toPrettyString)).mkString("Ordering: ",", ",""))

    //proof completion in dependency order
   val proofs =rm.foldLeft( Map[HOLFormula, LKProof]() )( (proofs_done, el) => {
     val (f, rules) = el
     val f_proof : LKProof = completeProof(f, proofs_done, naming, rules)
     proofs_done + ((f, f_proof))
    }
   )
   proofs
  }

  /* Creates the subproof proofname from a list of rules. Uses the naming function to create basic term and
  *  uses the proofs map to look up subproofs referenced by CONTINUEWITH and INSTLEMMA. This means, the calls
  *  to completeProof have to be ordered s.t. dependent proofs are already contained in the map.*/
  def completeProof(proofname : HOLFormula,
                    proofs : Map[HOLFormula, LKProof],
                    naming : String => HOLExpression,
                     rules : List[RToken]) : LKProof = {
    var proofstack : List[LKProof] = List[LKProof]()
    for ( rt@RToken(name, auxterm, antecedent, succedent) <- rules) {
      println("Processing rule: "+name)
      println(proofstack.mkString("Proof stack: ",",",""))
      val ant = antecedent.map(x => c(HLKHOLParser.ASTtoHOL( naming  ,x)))
      val suc = succedent.map(x  => c(HLKHOLParser.ASTtoHOL( naming  ,x)))
      val fs = FSequent(ant, suc)
      name match {
        case "AX" =>
          proofstack = Axiom(ant, suc) :: proofstack
        case "ALLL" =>
          proofstack = handleWeakQuantifier(name, proofstack, name, fs, auxterm, naming, rt)
        case "EXR" =>
          proofstack = handleWeakQuantifier(name, proofstack, name, fs, auxterm, naming, rt)
        case "ALLR" =>
          proofstack = handleStrongQuantifier(name, proofstack, name, fs, auxterm, naming, rt)
        case "EXL" =>
          proofstack = handleStrongQuantifier(name, proofstack, name, fs, auxterm, naming, rt)
        case "ANDR" =>
          proofstack = handleBinaryLogicalOperator(name, proofstack, name, fs, auxterm, naming, rt)
        case "ORL" =>
          proofstack = handleBinaryLogicalOperator(name, proofstack, name, fs, auxterm, naming, rt)


        case "CONTINUEWITH" => ;
        case "COMMENT" => ;
        case _ => throw new Exception("Rule type "+name+" not yet implemented!")
      }
    }

    require(proofstack.nonEmpty,"Error creating proof: Proof stack may not be empty!")
    proofstack.head
  }


  def handleWeakQuantifier(ruletype:String, current_proof: List[LKProof], name: String, fs: FSequent, auxterm: Option[LambdaAST], naming: (String) => HOLExpression, rt: RToken): List[LKProof] = {
    require(current_proof.size > 0, "Imbalanced proof tree in application of " + name + " with es: " + fs)
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
          HLKHOLParser.ASTtoHOL(naming, auxterm.getOrElse(throw new Exception("No substitution term found, please specify! " + rt)))
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

  def handleStrongQuantifier(ruletype:String, current_proof: List[LKProof], name: String, fs: FSequent, auxterm: Option[LambdaAST], naming: (String) => HOLExpression, rt: RToken): List[LKProof] = {
    require(current_proof.size > 0, "Imbalanced proof tree in application of " + name + " with es: " + fs)
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
          val t = HLKHOLParser.ASTtoHOL(naming, auxterm.getOrElse(throw new Exception("No substitution term found, please specify! " + rt)))
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

  def handleBinaryLogicalOperator(ruletype:String, current_proof: List[LKProof], name: String, fs: FSequent, auxterm: Option[LambdaAST], naming: (String) => HOLExpression, rt: RToken): List[LKProof] = {
    require(current_proof.size > 1, "Imbalanced proof tree in application of " + name + " with es: " + fs)
    val rightproof::leftproof::stack = current_proof

    val (mainsequent, auxsequent, context) = filterContext(leftproof.root.toFSequent, rightproof.root.toFSequent, fs)

    println("main   : " +  mainsequent)
    println("aux    : " +  auxsequent)
    println("context: " +  context)

    ruletype match {
      case "ANDR" =>
        mainsequent.succedent(0) match {
          case And(l,r) =>
            require(auxsequent.succedent.contains(l), "Left branch formula "+l+" not found in auxiliary formulas"+auxsequent)
            require(auxsequent.succedent.contains(r), "Right branch formula "+r+" not found in auxiliary formulas!"+auxsequent)
            require(leftproof.root.toFSequent.succedent.contains(l), "Left branch formula "+l+" not found in auxiliary formulas "+leftproof.root)
            require(rightproof.root.toFSequent.succedent.contains(r), "Right branch formula "+r+" not found in auxiliary formulas!"+rightproof.root)
            val inf = AndRightRule(leftproof, rightproof, l,r)
            val contr = contract(inf, fs)
            contr :: stack
          case _ => throw new Exception("Main formula of a conjunction right rule must have conjuntion as outermost operator!")
        }

      case "ORL"  =>
        mainsequent.antecedent(0) match {
          case Or(l,r) =>
            require(auxsequent.antecedent.contains(l), "Left branch formula "+l+" not found in auxiliary formulas "+auxsequent)
            require(auxsequent.antecedent.contains(r), "Right branch formula "+l+" not found in auxiliary formulas!"+auxsequent)
            require(leftproof.root.toFSequent.antecedent.contains(l), "Left branch formula "+l+" not found in auxiliary formulas "+leftproof.root)
            require(rightproof.root.toFSequent.antecedent.contains(r), "Right branch formula "+r+" not found in auxiliary formulas!"+rightproof.root)
            val inf = OrLeftRule(leftproof, rightproof, l,r)
            val contr = contract(inf, fs)
            contr :: stack
          case _ => throw new Exception("Main formula of a disjunction left rule must have disjunction as outermost operator!")
        }

      case "IMPL" =>
        mainsequent.antecedent(0) match {
          case Or(l,r) =>
            require(auxsequent.succedent.contains(l), "Left branch formula "+l+" not found in auxiliary formulas "+auxsequent)
            require(auxsequent.antecedent.contains(r), "Right branch formula "+r+" not found in auxiliary formulas!"+auxsequent)
            require(leftproof.root.toFSequent.antecedent.contains(l), "Left branch formula "+l+" not found in auxiliary formulas "+leftproof.root)
            require(rightproof.root.toFSequent.antecedent.contains(r), "Right branch formula "+r+" not found in auxiliary formulas!"+rightproof.root)
            val inf = ImpLeftRule(leftproof, rightproof, l,r)
            val contr = contract(inf, fs)
            contr :: stack
          case _ => throw new Exception("Main formula of a implication left rule must have implication as outermost operator!")
        }
    }
  }

  def contract(proof : LKProof, towhat : FSequent) : LKProof = {
    val context = proof.root.toFSequent diff towhat
    val leftcontr : LKProof = context.antecedent.foldLeft(proof)((intermediate, f) =>
      try {
        ContractionLeftRule(intermediate, f)
      } catch {
        case e : Exception =>
          throw new Exception("Could not contract "+f+" in "+proof.root+"!",e)
      }
    )
    val rightcontr : LKProof = context.succedent.foldLeft(leftcontr)((intermediate, f) =>
      try {
        ContractionLeftRule(intermediate, f)
      } catch {
        case e : Exception =>
          throw new Exception("Could not contract "+f+" in "+proof.root+"!",e)
      }
    )

    require(rightcontr.root.toFSequent.multiSetEquals( towhat ), "Context of contraction errenous: "+proof.root+" does not contract to "+rightcontr)

    rightcontr
  }

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

        case RToken("INSTLEMMA",Some(f),_,_) =>
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
        case RToken("INSTLEMMA",_,_,_) =>
          throw new Exception("The INSTLEMMA statement needs a proof as an argument!")
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

    require(ndiff.formulas.length == 1, "We want exactly one primary formula, not: "+ndiff)
    require(odiff.formulas.length > 0, "We want at least one auxiliary formula, not: "+odiff)
    (ndiff, odiff, csequent)
  }

  /* remove common context from 2 sequents (fs_old1, fs_old2) and inferred sequent (fs_new).
   * return a triple: (sequent with main formula,
   *                   sequent with auxiliary and uncontracted formulas,
   *                   context sequent) */
  def filterContext(fs_old1 : FSequent, fs_old2 : FSequent, fs_new : FSequent) : (FSequent, FSequent, FSequent) =
    filterContext(fs_old1 compose fs_old2, fs_new)


  private def c(e:HOLExpression) : HOLFormula =
    if (e.isInstanceOf[HOLFormula]) e.asInstanceOf[HOLFormula] else
      throw new Exception("Could not convert "+e+" to a HOL Formula!")

}
