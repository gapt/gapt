// TODO: shouldn't this go to parsing?

package at.logic.transformations.ceres.clauseSchema

import at.logic.algorithms.shlk.StepMinusOne
import at.logic.calculi.lk.base.{Sequent, LKProof}
import at.logic.calculi.slk._
import at.logic.language.lambda.types._
import at.logic.language.schema._
import collection.mutable.Map
import java.io.InputStreamReader
import scala.util.matching.Regex
import scala.util.parsing.combinator._

object ParseResSchema {
  def debugr[T<:Any](a:T) : T = { println("Debug: "+a); a}

  def apply(txt: InputStreamReader): Unit = {

    var map  = Map.empty[String, LKProof]
    var defMap = Map.empty[SchemaConst, Tuple2[List[IntegerTerm] ,SchemaFormula]]
    val mapPredicateToArity = Map.empty[String, Int]
    fo2SubstDB.clear
    resolutionProofSchemaDB.clear
    lazy val sp = new SimpleResolutionSchemaParser

    sp.parseAll(sp.resSchema, txt) match {
      case sp.Success(result, input) => // println("\n\nSUCCESS parse :) \n")
      case x: AnyRef => // { println("\n\nFAIL parse : \n"+error_buffer); throw new Exception("\n\nFAIL parse :( \n"); }
        throw new Exception(x.toString)
    }


    class SimpleResolutionSchemaParser extends JavaTokenParsers with at.logic.language.lambda.types.Parsers {

      def name = """[\\]*[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,_,0,1,2,3,4,5,6,7,8,9]*""".r

      def resSchema: Parser[Unit] =  rep(subst) ~ rep(trs) ~ rep(resTRS) ^^ {
        case rw_trs ~ res_trs  => {
        }
      }

      def subst: Parser[Unit] = "{" ~ fo2var ~ "<-" ~ "\\lambda" ~ index ~ "." ~ ( s_term | FOVariable | indexedVar | fo_term | FOConstant) ~ "}" ^^ {
        case "{" ~ z ~ "<-" ~ "\\lambda" ~ k ~ "." ~ sterm_or_fovar ~ "}" => {
          val h = SchemaAbs(k.asInstanceOf[SchemaVar], sterm_or_fovar)
          fo2SubstDB.add(z.asInstanceOf[fo2Var], h)
        }
      }
      //term-rewriting system for s-terms
      def trs: Parser[Unit] = (s_term | s_ind_term) ~ "->" ~ term ~ (s_term | s_ind_term) ~ "->" ~ term ^^ {
        case t1 ~ "->" ~ base ~ t2 ~ "->" ~ step => {
          t1 match {
            case sTerm(func1, i1, arg1) =>
              t2 match {
                case sTerm(func2, i2, arg2) => {
                  if (dbTRS.getOption(func1.asInstanceOf[SchemaConst]) == None || dbTRS.get(func1.asInstanceOf[SchemaConst]) == ((t1,base), (t2, step))) {
                    dbTRS.add(func1.asInstanceOf[SchemaConst], Tuple2(t1,base), Tuple2(t2, step))
                  } else throw new Exception("Cannot (re)define the function "+func1.asInstanceOf[SchemaConst].name.toString())
                }
              }
            case sIndTerm(func1, i1) =>
              t2 match {
                case sIndTerm(func2, i2) => {
                  if (dbTRS.getOption(func1) == None || dbTRS.get(func1) == ((t1,base), (t2, step))) {
                    dbTRS.add(func1, Tuple2(t1,base), Tuple2(t2, step))
                  } else throw new Exception("Cannot (re)define the function "+func1.name.toString())
                }
              }
          }
        }
      }

      // a usual clause
      def non_varSclause: Parser[sClause] = rep(atom) ~ "|-" ~ rep(atom) ^^ {
        case ant ~ "|-" ~ succ => nonVarSclause(ant, succ)
      }

      // clause variable
      def sclause_var: Parser[sClause] = "[X,Y]" ^^ {
        case str => sClauseVar(str)
      }

      //resolution term inductive definition
      def res_term: Parser[sResolutionTerm] = r_term | non_varSclause | rho_term

      //rTerm
      def r_term: Parser[sResolutionTerm] = "r" ~ "(" ~ res_term ~ ";" ~ res_term ~ ";" ~ atom ~ ")" ^^ {
        case "r" ~ "(" ~ res_term1 ~ ";" ~ res_term2 ~ ";" ~ at ~ ")" => rTerm(res_term1, res_term2, at)
      }

      // TODO: X is missing
      def rho_term: Parser[sResolutionTerm] = "\\rho"~"""[_]*[0-9]*""".r ~ "(" ~ index ~ "," ~ fo2var ~ ")" ^^ {
        case "\\rho"~str ~ "(" ~ ind ~ "," ~ fo2v ~ ")" =>
          ResolutionProofSchema("\\rho"+str, ind::fo2v::Nil)
      }

      def fo2var: Parser[SchemaVar] = """[z][_]*[0-9]*""".r ^^ {
        case str => {
          fo2Var(str)
        }
      }

      def r_term_OR_clause: Parser[sResolutionTerm] = non_varSclause | r_term

      //term-rewriting system for r-terms
      def resTRS: Parser[Any] = rho_term ~ "->" ~ r_term_OR_clause ~ rho_term ~ "->" ~ r_term ^^ {
        case rho1 ~ "->" ~ base ~ rho2 ~ "->" ~ step => {
          rho1 match {
            case ResolutionProofSchema(name, arg1) =>
              rho2 match {
                case ResolutionProofSchema(name1, arg2) => {
                  //                  if(name == name1) {
                  resolutionProofSchemaDB.add(name, Tuple2(rho1, base), Tuple2(rho2, step))
                  //                  }
                }
              }
          }
        }
      }

      def label: String = """[0-9]*[root]*"""

      def term: Parser[SchemaExpression] = ( non_formula | formula)
      def formula: Parser[SchemaFormula] = (atom | neg | and | or | imp | forall | exists | variable | constant) ^? {case trm => trm.asInstanceOf[SchemaFormula]}
      def intTerm: Parser[SchemaExpression] = index | sumIntTerm | s_ind_term    
      def sumIntTerm: Parser[SchemaExpression] = s_ind_term ~ "+" ~ intConst ^^ {
          case t ~ "+" ~ c => Succ(t)
        }
      def index: Parser[SchemaExpression] = (sum | intConst | intVar | succ )
      def intConst: Parser[IntegerTerm] = """[0-9]+""".r ^^ { case x => { toIntegerTerm(x.toInt).asInstanceOf[IntegerTerm] }} 

      def sum : Parser[IntegerTerm] = intVar ~ "+" ~ intConst ^^ {case indV ~ "+" ~ indC => {
        StepMinusOne.indVarPlusIndConst(indV, indC)
      }}

      def intVar: Parser[IntVar] = "[i,j,n,k,x]".r ^^ {
        case x => { IntVar(x) }
      }
      def succ: Parser[SchemaExpression] = "s(" ~ intTerm ~ ")" ^^ {
        case "s(" ~ intTerm ~ ")" => Succ(intTerm)
      }

      def schemaFormula = formula

      def non_formula: Parser[SchemaExpression] = (fo_term | s_ind_term | s_term | indexedVar | abs | variable | index | constant | var_func | const_func )
      def first: Parser[SchemaExpression] = s_ind_term | index
      def s_term: Parser[SchemaExpression] = """[g,h]""".r ~ "(" ~ first ~ s_term_rest ^^ {
        case name ~ "(" ~ i ~ args => {
          sTerm(name.asInstanceOf[String], i, args.asInstanceOf[List[SchemaExpression]])
        }
      }

      def s_ind_term: Parser[SchemaExpression] = "m" ~ "(" ~ intTerm ~ ")" ^^ {
        case name ~ "(" ~ i ~ ")" => {
          sIndTerm(name.asInstanceOf[String], i.asInstanceOf[IntegerTerm])
        }
      }

      def s_term_rest: Parser[List[SchemaExpression]] = s_term_rest_end | s_term_rest_args

      def s_term_rest_end: Parser[List[SchemaExpression]] = ")" ^^ {
        case ")" => Nil
      }

      def s_term_rest_args: Parser[List[SchemaExpression]] = "," ~ repsep(non_formula, ",") ~ ")" ^^ {
        case "," ~ l ~ ")" => l.asInstanceOf[List[SchemaExpression]]
      }

      def fo_term: Parser[SchemaExpression] = "[f]".r ~ "(" ~ non_formula ~ ")" ^^ {
        case name ~ "(" ~ arg ~ ")" => {
          foTerm(name, arg::Nil)
        }
      }
      def indexedVar: Parser[SchemaVar] = "z"  ~ "(" ~ intTerm ~ ")" ^^ {
        case x ~ "(" ~ index ~ ")" => {
          indexedFOVar(x, index)
        }
      }

      // TODO: a should be a FOConstant
      def FOVariable: Parser[SchemaVar] = regex(new Regex("[x,y]" + word))  ^^ {case x => foVar(x)}
      def FOConstant: Parser[SchemaConst] = regex(new Regex("[a]" + word))  ^^ {case x => foConst(x)}
      def variable: Parser[SchemaVar] = (indexedVar | FOVariable)//regex(new Regex("[u-z]" + word))  ^^ {case x => hol.createVar(new VariableStringSymbol(x), i->i).asInstanceOf[SchemaVar]}
      def constant: Parser[SchemaConst] = FOConstant//regex(new Regex("[a-tA-Z0-9]" + word))  ^^ {case x => hol.createVar(new ConstantStringSymbol(x), ind->ind).asInstanceOf[SchemaConst]}
      def and: Parser[SchemaFormula] = "(" ~ repsep(formula, "/\\") ~ ")" ^^ { case "(" ~ formulas ~ ")"  => { formulas.tail.foldLeft(formulas.head)((f,res) => And(f, res)) } }
      def or: Parser[SchemaFormula]  = "(" ~ repsep(formula, """\/""" ) ~ ")" ^^ { case "(" ~ formulas ~ ")"  => { formulas.tail.foldLeft(formulas.head)((f,res) => Or(f, res)) } }
      def imp: Parser[SchemaFormula] = "Imp" ~ formula ~ formula ^^ {case "Imp" ~ x ~ y => Imp(x,y)}
      def abs: Parser[SchemaExpression] = "Abs" ~ variable ~ term ^^ {case "Abs" ~ v ~ x => SchemaAbs(v,x)}
      def neg: Parser[SchemaFormula] = "~" ~ formula ^^ {case "~" ~ x => Neg(x)}
      def atom: Parser[SchemaFormula] = (equality | var_atom | const_atom)
      def forall: Parser[SchemaFormula] = "Forall" ~ variable ~ formula ^^ {case "Forall" ~ v ~ x => AllVar(v,x)}
      def exists: Parser[SchemaFormula] = "Exists" ~ variable ~ formula ^^ {case "Exists" ~ v ~ x => ExVar(v,x)}
      def var_atom: Parser[SchemaFormula] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {
        val h = SchemaVar(x, FunctionType(To, params.map(_.exptype)))
        Atom(h, params)
      }}

      def const_atom: Parser[SchemaFormula] = regex(new Regex("P")) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {
        val h = SchemaConst(x, FunctionType(To, params.map(_.exptype)))
        Atom(h, params)
      }}
      def equality: Parser[SchemaFormula] = /*eq_infix | */ eq_prefix // infix is problematic in higher order
      def eq_prefix: Parser[SchemaFormula] = "=" ~ "(" ~ term ~ "," ~ term  ~ ")" ^^ {case "=" ~ "(" ~ x ~ "," ~ y  ~ ")" => Equation(x,y)}
      def var_func: Parser[SchemaExpression] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")"  => 
        val h = SchemaVar(x, ->(Tindex, Tindex))
        Function(h, params)
      }
      def const_func: Parser[SchemaExpression] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")"  ^^ {case x ~ "(" ~ params ~ ")"  => 
        val h = SchemaConst(x, ->(Tindex, Tindex))
        Function(h, params)
      }
      protected def word: String = """[a-zA-Z0-9$_{}]*"""
      protected def symbol: Parser[String] = symbols.r
      def symbols: String = """[\053\055\052\057\0134\0136\074\076\075\0140\0176\077\0100\046\0174\041\043\047\073\0173\0175]+""" // +-*/\^<>=`~?@&|!#{}';


      def proof_name : Parser[String] = """[\\]*[a-z]*[0-9]*""".r


      def termDefL1: Parser[LKProof] = "termDefL1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "termDefL1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          TermLeftEquivalenceRule1(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
        }
      }

      def termDefR1: Parser[LKProof] = "termDefR1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "termDefR1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          TermRightEquivalenceRule1(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
        }
      }
    }
  }
}



//------------------------------------



object ParseResSchemaDavid {
  def debugr[T<:Any](a:T) : T = { println("Debug: "+a); a}

  def apply(txt: InputStreamReader): Unit = {

    var map  = Map.empty[String, LKProof]
    var defMap = Map.empty[SchemaConst, Tuple2[List[IntegerTerm] ,SchemaFormula]]
    val mapPredicateToArity = Map.empty[String, Int]
    fo2SubstDB.clear
    resolutionProofSchemaDB.clear
    lazy val sp = new SimpleResolutionSchemaParser

    sp.parseAll(sp.resSchema, txt) match {
      case sp.Success(result, input) => 
      case x: AnyRef => 
        throw new Exception(x.toString)
    }


    class SimpleResolutionSchemaParser extends JavaTokenParsers with at.logic.language.lambda.types.Parsers {

      def name = """[\\]*[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,_,0,1,2,3,4,5,6,7,8,9]*""".r

      def resSchema: Parser[Unit] =  /*rep(subst) ~*/ rep(trs) ~ rep(resTRS) ^^ {
        case rw_trs ~ res_trs  => {
        }
      }

      def subst: Parser[Unit] = "{" ~ fo2var ~ "<-" ~ "\\lambda" ~ index ~ "." ~ ( s_term | FOVariable | indexedVar | fo_term | FOConstant) ~ "}" ^^ {
        case "{" ~ z ~ "<-" ~ "\\lambda" ~ k ~ "." ~ sterm_or_fovar ~ "}" => {
          val h = SchemaAbs(k.asInstanceOf[SchemaVar], sterm_or_fovar)
          fo2SubstDB.add(z.asInstanceOf[fo2Var], h)
        }
      }
      //term-rewriting system for s-terms
      def trs: Parser[Unit] = (s_term | s_ind_term) ~ "->" ~ term ~ (s_term | s_ind_term) ~ "->" ~ term ^^ {
        case t1 ~ "->" ~ base ~ t2 ~ "->" ~ step => {
          t1 match {
            case sTerm(func1, i1, arg1) =>
              t2 match {
                case sTerm(func2, i2, arg2) => {
                  if (dbTRS.getOption(func1.asInstanceOf[SchemaConst]) == None || dbTRS.get(func1.asInstanceOf[SchemaConst]) == ((t1,base), (t2, step))) {
                    dbTRS.add(func1.asInstanceOf[SchemaConst], Tuple2(t1,base), Tuple2(t2, step))
                  } else throw new Exception("Cannot (re)define the function "+func1.asInstanceOf[SchemaConst].name.toString())
                }
              }
            case sIndTerm(func1, i1) =>
              t2 match {
                case sIndTerm(func2, i2) => {
                  if (dbTRS.getOption(func1) == None || dbTRS.get(func1) == ((t1,base), (t2, step))) {
                    dbTRS.add(func1, Tuple2(t1,base), Tuple2(t2, step))
                  } else throw new Exception("Cannot (re)define the function "+func1.name.toString())
                }
              }
          }
        }
      }

      // a usual clause
      def non_varSclause: Parser[sClause] = rep(atom) ~ "|-" ~ rep(atom) ^^ {
        case ant ~ "|-" ~ succ => nonVarSclause(ant, succ)
      }

      // clause variable
      def sclause_var: Parser[sClause] = "[X,Y]" ^^ {
        case str => sClauseVar(str)
      }

      //resolution term inductive definition
      def res_term: Parser[sResolutionTerm] = r_term | non_varSclause | rho_term

      //rTerm
      def r_term: Parser[sResolutionTerm] = "r" ~ "(" ~ res_term ~ ";" ~ res_term ~ ";" ~ atom ~ ")" ^^ {
        case "r" ~ "(" ~ res_term1 ~ ";" ~ res_term2 ~ ";" ~ at ~ ")" => rTerm(res_term1, res_term2, at)
      }

      // TODO: X is missing
      def rho_term: Parser[sResolutionTerm] = "\\rho"~"""[_]*[0-9]*""".r ~ "(" ~ index ~ "," ~ rep(fo2var) ~ ")" ^^ {
        case "\\rho"~str ~ "(" ~ ind ~ "," ~ fo2v ~ ")" =>
          ResolutionProofSchema("\\rho"+str, ind::fo2v)
      }

      def fo2var: Parser[SchemaVar] = """[z][_]*[0-9]*""".r ^^ {
        case str => {
          fo2Var(str)
        }
      }

      def r_term_OR_clause: Parser[sResolutionTerm] = non_varSclause | r_term

      //term-rewriting system for r-terms
      def resTRS: Parser[Any] = rho_term ~ "->" ~ r_term_OR_clause ~ rho_term ~ "->" ~ r_term ^^ {
        case rho1 ~ "->" ~ base ~ rho2 ~ "->" ~ step => {
          rho1 match {
            case ResolutionProofSchema(name, arg1) =>
              rho2 match {
                case ResolutionProofSchema(name1, arg2) => {
                  resolutionProofSchemaDB.add(name, Tuple2(rho1, base), Tuple2(rho2, step))
                }
              }
          }
        }
      }

      def label: String = """[0-9]*[root]*"""

      def term: Parser[SchemaExpression] = ( non_formula | MULTterm | PLUSterm | MINUSterm)
      def formula: Parser[SchemaFormula] = (atom | neg | and | or | imp | forall | exists | variable | constant) ^? {case trm => trm.asInstanceOf[SchemaFormula]}
      def intTerm: Parser[SchemaExpression] = index | sumIntTerm | s_ind_term 
      def sumIntTerm: Parser[SchemaExpression] = s_ind_term ~ "+" ~ intConst ^^ {
          case t ~ "+" ~ c => Succ(t)
        }
      def index: Parser[SchemaExpression] = (sum | intConst | intVar | succ )
      def intConst: Parser[IntegerTerm] = """[0-9]+""".r ^^ { case x => { toIntegerTerm(x.toInt).asInstanceOf[IntegerTerm] }} 

      def sum : Parser[IntegerTerm] = intVar ~ "+" ~ intConst ^^ {case indV ~ "+" ~ indC => {
        StepMinusOne.indVarPlusIndConst(indV, indC)
      }}

      def intVar: Parser[IntVar] = "[i,j,n,k,x]".r ^^ {
        case x => { /*println("\n\nintVar");*/ IntVar(x)}
      }
      def succ: Parser[SchemaExpression] = "s(" ~ intTerm ~ ")" ^^ {
        case "s(" ~ intTerm ~ ")" => Succ(intTerm)
      }

      def schemaFormula = formula

      def non_formula: Parser[SchemaExpression] = (fo_term | s_ind_term | s_term | indexedVar | abs | variable | index | constant | var_func | const_func )
      def first: Parser[SchemaExpression] = s_ind_term | index
      def s_term: Parser[SchemaExpression] = """[g,h]""".r ~ "(" ~ first ~ s_term_rest ^^ {
        case name ~ "(" ~ i ~ args => {
          sTerm(name.asInstanceOf[String], i, args.asInstanceOf[List[SchemaExpression]])
        }
      }

      def s_ind_term: Parser[SchemaExpression] = "m" ~ "(" ~ intTerm ~ ")" ^^ {
        case name ~ "(" ~ i ~ ")" => {
          sIndTerm(name.asInstanceOf[String], i.asInstanceOf[IntegerTerm])
        }
      }

      def s_term_rest: Parser[List[SchemaExpression]] = s_term_rest_end | s_term_rest_args

      def s_term_rest_end: Parser[List[SchemaExpression]] = ")" ^^ {
        case ")" => Nil
      }

      def s_term_rest_args: Parser[List[SchemaExpression]] = "," ~ repsep(non_formula, ",") ~ ")" ^^ {
        case "," ~ l ~ ")" => l.asInstanceOf[List[SchemaExpression]]
      }

      def fo_term: Parser[SchemaExpression] = "[f]".r ~ "(" ~ non_formula ~ ")" ^^ {
        case name ~ "(" ~ arg ~ ")" => {
          foTerm(name, arg::Nil)
        }
      }
      def indexedVar: Parser[SchemaVar] = "z"  ~ "(" ~ intTerm ~ ")" ^^ {
        case x ~ "(" ~ index ~ ")" => {
          indexedFOVar(x, index)
        }
      }

      // TODO: a should be a FOConstant
      def FOVariable: Parser[SchemaVar] = regex(new Regex("[x,y]" + word))  ^^ {case x => foVar(x)}
      def FOConstant: Parser[SchemaConst] = regex(new Regex("[a,p]" + word))  ^^ {case x => foConst(x)}
      def variable: Parser[SchemaVar] = (indexedVar | FOVariable)
      def constant: Parser[SchemaConst] = FOConstant
      def and: Parser[SchemaFormula] = "(" ~ repsep(formula, "/\\") ~ ")" ^^ { case "(" ~ formulas ~ ")"  => { formulas.tail.foldLeft(formulas.head)((f,res) => And(f, res)) } }
      def or: Parser[SchemaFormula]  = "(" ~ repsep(formula, """\/""" ) ~ ")" ^^ { case "(" ~ formulas ~ ")"  => { formulas.tail.foldLeft(formulas.head)((f,res) => Or(f, res)) } }
      def imp: Parser[SchemaFormula] = "Imp" ~ formula ~ formula ^^ {case "Imp" ~ x ~ y => Imp(x,y)}
      def abs: Parser[SchemaExpression] = "Abs" ~ variable ~ term ^^ {case "Abs" ~ v ~ x => SchemaAbs(v,x).asInstanceOf[SchemaExpression]}
      def neg: Parser[SchemaFormula] = "~" ~ formula ^^ {case "~" ~ x => Neg(x)}
      def atom: Parser[SchemaFormula] = (equality | var_atom | const_atom | less | lessOrEqual)
      def forall: Parser[SchemaFormula] = "Forall" ~ variable ~ formula ^^ {case "Forall" ~ v ~ x => AllVar(v,x)}
      def exists: Parser[SchemaFormula] = "Exists" ~ variable ~ formula ^^ {case "Exists" ~ v ~ x => ExVar(v,x)}
      def var_atom: Parser[SchemaFormula] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {
        val h = SchemaVar(x, FunctionType(To, params.map(_.exptype)))
        Atom(h, params)
      }}

      def const_atom: Parser[SchemaFormula] = regex(new Regex("P")) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {
        val h = SchemaConst(x, FunctionType(To, params.map(_.exptype)))
        Atom(h, params)
      }}
      def equality: Parser[SchemaFormula] = /*eq_infix | */ eq_prefix // infix is problematic in higher order
      //def eq_infix: Parser[SchemaFormula] = term ~ "=" ~ term ^^ {case x ~ "=" ~ y => Equation(x,y)}
      def less: Parser[SchemaFormula] = term ~ "<" ~ term ^^ {case x ~ "<" ~ y => lessThan(x,y)}
      def lessOrEqual: Parser[SchemaFormula] = term ~ "<=" ~ term ^^ {case x ~ "<=" ~ y => leq(x,y)}
      def eq_prefix: Parser[SchemaFormula] = "=" ~ "(" ~ term ~ "," ~ term  ~ ")" ^^ {case "=" ~ "(" ~ x ~ "," ~ y  ~ ")" => Equation(x,y)}
      def var_func: Parser[SchemaExpression] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")"  => 
        val h = SchemaVar(x, ->(Tindex, Tindex))
        Function(h, params)
      }
      def const_func: Parser[SchemaExpression] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")"  ^^ {case x ~ "(" ~ params ~ ")"  => 
        val h = SchemaConst(x, ->(Tindex, Tindex))
        Function(h, params)
      }
      protected def word: String = """[a-zA-Z0-9$_{}]*"""
      protected def symbol: Parser[String] = symbols.r
      def symbols: String = """[\053\055\052\057\0134\0136\074\076\075\0140\0176\077\0100\046\0174\041\043\047\073\0173\0175]+""" // +-*/\^<>=`~?@&|!#{}';


      def proof_name : Parser[String] = """[\\]*[a-z]*[0-9]*""".r


      def termDefL1: Parser[LKProof] = "termDefL1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "termDefL1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          TermLeftEquivalenceRule1(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
        }
      }

      def termDefR1: Parser[LKProof] = "termDefR1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "termDefR1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          TermRightEquivalenceRule1(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
        }
      }
      def MULTterm: Parser[SchemaExpression] = "(" ~ term ~ "*" ~ term ~ ")" ^^ {
        case "(" ~ t1 ~ "*" ~ t2 ~ ")" => {
          val func = SchemaConst("*", ->(Tindex, ->(Tindex , Tindex)))
          Function(func, t1::t2::Nil)
        }
      }
      def PLUSterm: Parser[SchemaExpression] = "(" ~ term ~ "+" ~ term ~ ")" ^^ {
        case "(" ~ t1 ~ "+" ~ t2 ~ ")" => {
          val func = SchemaConst("+", ->(Tindex, ->(Tindex , Tindex)))
          Function(func, t1::t2::Nil)
        }
      }
      def MINUSterm: Parser[SchemaExpression] = "(" ~ term ~ "-" ~ term ~ ")" ^^ {
        case "(" ~ t1 ~ "-" ~ t2 ~ ")" => {
          val func = SchemaConst("-", ->(Tindex, ->(Tindex , Tindex)))
          Function(func, t1::t2::Nil)
        }
      }
    }
  }
}


