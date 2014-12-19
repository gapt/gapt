package at.logic.parsing.shlk_parsing

import scala.util.parsing.combinator._
import scala.util.matching.Regex
import java.io.InputStreamReader
import at.logic.language.schema._
import at.logic.calculi.lk.base.{FSequent, Sequent, LKProof}
import collection.mutable.{Map => MMap}
import at.logic.calculi.slk._
import scala.Tuple4
import at.logic.language.schema.IntZero
import scala.Tuple2
import at.logic.language.lambda.symbols.StringSymbol
import at.logic.language.lambda.types.{To, FunctionType, Tindex, Ti}
import at.logic.calculi.lk._

object SHLK {

  def parseProofs(input: InputStreamReader): List[(String, LKProof)] = {
//    ("p",parseProof(input, "root"))::Nil
    val m = SHLK.parseProof(input)
    m.foldLeft(List.empty[(String, LKProof)])((res, pair) => (pair._1, pair._2._1.get("root").get) :: (pair._1, pair._2._2.get("root").get) :: res)
  }

  //--------------------------------- parse SLK sequent ----------------------


  def parseSequent(txt: String): FSequent = {
    lazy val sp = new SequentParser
    sp.parseAll(sp.sequent, txt) match {
      case res @ sp.Success(result, input) => {
//        println("\n\nSUCCESS parse :) \n")
        return res.result.toFSequent
      }
      case x: AnyRef => // { println("\n\nFAIL parse : \n"+error_buffer); throw new Exception("\n\nFAIL parse :( \n"); }
        throw new Exception("Error in SHLK.parseSequent : "+x.toString)
    }
    class SequentParser extends JavaTokenParsers with at.logic.language.lambda.types.Parsers {
      def name = """[\\]*[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,_,0,1,2,3,4,5,6,7,8,9]*""".r
      def term: Parser[SchemaExpression] = ( non_formula | formula)
      def formula: Parser[SchemaFormula] = (atom | neg | big | and | or | indPred | imp | forall | exists | variable | constant) ^? {case trm: SchemaFormula => trm }
      def intTerm: Parser[SchemaExpression] = (index | schemaFormula)
      def index: Parser[IntegerTerm] = (sum | intConst | intVar | succ  )
      def intConst: Parser[IntegerTerm] = (intZero | intOne | intTwo | intThree)
      def intOne :  Parser[IntegerTerm] = "1".r ^^ { case x => {  Succ(IntZero())}}
      def intTwo :  Parser[IntegerTerm] = "2".r ^^ { case x => {  Succ(Succ(IntZero()))}}
      def intThree: Parser[IntegerTerm] = "3".r ^^ { case x => {  Succ(Succ(Succ(IntZero())))}}
      def intZero:  Parser[IntegerTerm] = "0".r ^^ { case x => {  IntZero()}
      }
      def sum : Parser[IntegerTerm] = intVar ~ "+" ~ intConst ^^ {case indV ~ "+" ~ indC => {
        //        println("\n\nsum")
        indC match {
          case Succ(IntZero()) => Succ(indV)
          case Succ(Succ(IntZero())) => Succ(Succ(indV))
          case Succ(Succ(Succ(IntZero()))) => Succ(Succ(Succ(indV)))
        }}}
      def intVar: Parser[IntVar] = "[i,j,m,n,k,x]".r ^^ {
        case x => { /*println("\n\nintVar");*/ IntVar(x)}
      }
      def succ: Parser[IntegerTerm] = "s(" ~ intTerm ~ ")" ^^ {
        case "s(" ~ intTerm ~ ")" => Succ(intTerm.asInstanceOf[IntegerTerm])
      }
      def schemaFormula = formula
      def indPred : Parser[SchemaFormula] = """[A-Z]*[a-z]*[0-9]*""".r ~ "(" ~ index ~ "," ~ s_term ~ ")" ^^ {
        case x ~ "(" ~ l ~ "," ~ t ~ ")" => {
          println("\n\nt = "+t)
          IndexedPredicate(x, l)
        }
      }
//      def indPred : Parser[HOLFormula] = """[A-Z]*[a-z]*[0-9]*""".r ~ "(" ~ repsep(index,",") ~ ")" ^^ {
//        case x ~ "(" ~ l ~ ")" => {
//          IndexedPredicate(new ConstantStringSymbol(x), l)
//        }
//      }

      // nested bigAnd bigOr....           ("""BigAnd""".r | """BigOr""".r)
      def prefix : Parser[Tuple4[Boolean, IntVar, IntegerTerm, IntegerTerm]] = """[BigAnd]*[BigOr]*""".r ~ "(" ~ intVar ~ "=" ~ index ~ ".." ~ index ~ ")" ^^ {
        case "BigAnd" ~ "(" ~ intVar1 ~ "=" ~ ind1 ~ ".." ~ ind2 ~ ")"  => {
          Tuple4(true, intVar1, ind1, ind2)
        }
        case "BigOr" ~ "(" ~ intVar1 ~ "=" ~ ind1 ~ ".." ~ ind2 ~ ")"  => {
          Tuple4(false, intVar1, ind1, ind2)
        }
      }
      def big : Parser[SchemaFormula] = rep1(prefix) ~ schemaFormula ^^ {
        case l ~ schemaFormula  => {
          l.reverse.foldLeft(schemaFormula.asInstanceOf[SchemaFormula])((res, triple) => {
            if (triple._1)
              BigAnd(triple._2, res, triple._3, triple._4)
            else
              BigOr(triple._2, res, triple._3, triple._4)
          })
        }
      }
      def non_formula: Parser[SchemaExpression] = (s_term | indexedVar | abs | variable | constant | var_func | const_func)
      def s_term: Parser[SchemaExpression] = "[f,g,h]".r ~ "(" ~ intTerm ~ "," ~ variable ~ ")" ^^ {
        case name ~ "(" ~ i ~ "," ~ args ~ ")" => {
          println("\n\nsTerm\n")
          sTerm(name, i.asInstanceOf[IntegerTerm], args::Nil)
        }
      }
      def indexedVar: Parser[SchemaVar] = regex(new Regex("[u-z]")) ~ "(" ~ intTerm ~ ")" ^^ {
        case x ~ "(" ~ index ~ ")" => SchemaFactory.createVar(StringSymbol(x), Tindex -> Ti)
      }
      def FOVariable: Parser[SchemaVar] = regex(new Regex("[u-z]" + word))  ^^ {case x => SchemaFactory.createVar(StringSymbol(x), Ti)}
      def variable: Parser[SchemaVar] = FOVariable//regex(new Regex("[u-z]" + word))  ^^ {case x => hol.createVar(new VariableStringSymbol(x), i->i).asInstanceOf[SchemaVar]}
      def constant: Parser[SchemaConst] = regex(new Regex("[a-tA-Z0-9]" + word))  ^^ {case x => SchemaFactory.createConst(StringSymbol(x), Tindex -> Tindex)}
      def and: Parser[SchemaFormula] = "(" ~ repsep(formula, "/\\") ~ ")" ^^ { case "(" ~ formulas ~ ")"  => { formulas.tail.foldLeft(formulas.head)((f,res) => And(f, res)) } }
      def or: Parser[SchemaFormula]  = "(" ~ repsep(formula, """\/""" ) ~ ")" ^^ { case "(" ~ formulas ~ ")"  => { formulas.tail.foldLeft(formulas.head)((f,res) => Or(f, res)) } }
      def imp: Parser[SchemaFormula] = "Imp" ~ formula ~ formula ^^ {case "Imp" ~ x ~ y => Imp(x,y)}
      def abs: Parser[SchemaExpression] = "Abs" ~ variable ~ term ^^ {case "Abs" ~ v ~ x => SchemaAbs(v,x).asInstanceOf[SchemaExpression]}
      def neg: Parser[SchemaFormula] = "~" ~ formula ^^ {case "~" ~ x => Neg(x)}
      def atom: Parser[SchemaFormula] = (equality | var_atom | const_atom)
      def forall: Parser[SchemaFormula] = "Forall" ~ variable ~ formula ^^ {case "Forall" ~ v ~ x => AllVar(v,x)}
      def exists: Parser[SchemaFormula] = "Exists" ~ variable ~ formula ^^ {case "Exists" ~ v ~ x => ExVar(v,x)}
      def var_atom: Parser[SchemaFormula] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {
        Atom(SchemaVar(x, FunctionType(To, params map (_.exptype) )), params)
      }}

      def const_atom: Parser[SchemaFormula] = regex(new Regex("P")) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {

        //        println("\n\nconst_atom")
         Atom(SchemaConst(x, FunctionType(To, params map (_.exptype) )), params)
      }}
      def equality: Parser[SchemaFormula] = /*eq_infix | */ eq_prefix // infix is problematic in higher order
      //def eq_infix: Parser[SchemaFormula] = term ~ "=" ~ term ^^ {case x ~ "=" ~ y => Equation(x,y)}
      def eq_prefix: Parser[SchemaFormula] = "=" ~ "(" ~ term ~ "," ~ term  ~ ")" ^^ {case "=" ~ "(" ~ x ~ "," ~ y  ~ ")" => Equation(x,y)}
      def var_func: Parser[SchemaExpression] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {
        case x ~ "(" ~ params ~ ")"  =>
          //TODO: check if the return type should really be Tindex->Tindex, it is in the old code but that may not be general enough
          Function(SchemaVar(x, FunctionType(Tindex -> Tindex, params.map(_.exptype))), params)
      }
      def const_func: Parser[SchemaExpression] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")"  ^^ {case x ~ "(" ~ params ~ ")"  =>
        Function(SchemaConst(x, FunctionType(Tindex->Tindex, params map (_.exptype))), params)}
      protected def word: String = """[a-zA-Z0-9$_{}]*"""
      protected def symbol: Parser[String] = symbols.r
      def symbols: String = """[\053\055\052\057\0134\0136\074\076\075\0140\0176\077\0100\046\0174\041\043\047\073\0173\0175]+""" // +-*/\^<>=`~?@&|!#{}';

      def sequent: Parser[Sequent] = repsep(formula,",") ~ "|-" ~ repsep(formula,",") ^^ { case lfs ~ "|-" ~ rfs => {
          Axiom(lfs, rfs).root
        }
      }
    }
    throw new Exception("\nError in SHLK.parseSequent function !\n")
  }
  

//--------------------------------- parse SLK proof -----------------------

  //plabel should return the proof corresponding to this label
  def parseProof(txt: InputStreamReader): MMap[String, Tuple2[MMap[String, LKProof], MMap[String, LKProof]]] = {
    var mapBase = MMap.empty[String, LKProof]
    var mapStep = MMap.empty[String, LKProof]
    var map  = MMap.empty[String, LKProof]
    var baseORstep: Int = 1
    SchemaProofDB.clear
    var defMMap = MMap.empty[SchemaConst, Tuple2[List[IntegerTerm] ,SchemaFormula]]
    var list = List[String]()
    var error_buffer = ""
//    lazy val sp2 = new ParserTxt
//    sp2.parseAll(sp2.line, txt)
    val bigMMap = MMap.empty[String, Tuple2[MMap[String, LKProof], MMap[String, LKProof]]]
    val mapPredicateToArity = MMap.empty[String, Int]
    lazy val sp = new SimpleSLKParser

//    var proofName = ""
//    sp.parseAll(sp.line, txt)
    sp.parseAll(sp.slkProofs, txt) match {
      case sp.Success(result, input) => // println("\n\nSUCCESS parse :) \n")
      case x: AnyRef => // { println("\n\nFAIL parse : \n"+error_buffer); throw new Exception("\n\nFAIL parse :( \n"); }
        throw new Exception(x.toString)
    }

//    class ParserTxt extends JavaTokenParsers with at.logic.language.lambda.types.Parsers {
//
//      def line: Parser[List[Unit]] = repsep(mapping,"\n")
//
//      def mapping: Parser[Unit] = """*""".r ^^ {
//        case t => {
//          list = t :: list
//        }
//      }
//    }

    class SimpleSLKParser extends JavaTokenParsers with at.logic.language.lambda.types.Parsers {

      def line: Parser[List[Unit]] = rep(mappingBase)

      def mappingBase: Parser[Unit] = label.r ~ ":" ~ proof ^^ {
        case l ~ ":" ~ p => {
          error_buffer = l
          if (baseORstep == 2) {
            map = MMap.empty[String, LKProof]
            baseORstep = 1
          }
          map.put(l,p)
          mapBase = map
        }
      }

      def mappingStep: Parser[Unit] = label.r ~ ":" ~ proof ^^ {
        case l ~ ":" ~ p => {
          error_buffer = l
//          mapStep.put(l,p)
          if (baseORstep == 1) {
            map = MMap.empty[String, LKProof]
            baseORstep = 2
          }
          map.put(l,p)
          mapStep = map
        }
      }

      def name = """[\\]*[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,_,0,1,2,3,4,5,6,7,8,9]*""".r

      def slkProof: Parser[Unit] = "proof" ~ name ~ "proves" ~ sequent ~ "base" ~ "{" ~ line  ~ "}" ~ "step" ~ "{" ~ rep(mappingStep) ~ "}"  ^^ {
        case                       "proof" ~  str ~ str1 ~      seq    ~ "base" ~ "{" ~ line1 ~ "}" ~ "step" ~ "{" ~     line2        ~ "}" => {
//          proofName = str
          bigMMap.put(str, Tuple2(mapBase, mapStep))
          SchemaProofDB.put(new SchemaProof(str, IntVar("k")::Nil, seq.toFSequent, mapBase.get("root").get, mapStep.get("root").get))
          mapBase = MMap.empty[String, LKProof]
          mapStep = MMap.empty[String, LKProof]
//          println("\n\nParsing is SUCCESSFUL : "+str)
        }
      }


      def slkProofs: Parser[List[Unit]] =  rep(define) ~ rep(slkProof) ^^ {
         case a ~ s  => {
          List.empty[Unit]
        }
      }

      def proof: Parser[LKProof] = ax | orL | orR1 | orR | orR2 | negL | negR | cut | pLink | andL | andR| andL1 | andL2 | weakL | weakR | contrL | contrR | andEqR1 | andEqR2 | andEqR3 | orEqR1 | orEqR2 | orEqR3 | andEqL1 | andEqL2 | andEqL3 | orEqL1 | orEqL2 | orEqL3
      def label: String = """[0-9]*[root]*"""

      def term: Parser[SchemaExpression] = ( non_formula | formula)
      def formula: Parser[SchemaFormula] = (neg | big | and | or | indPred | imp | forall | exists | variable | constant) ^? {case trm: SchemaFormula => trm}

      def intTerm: Parser[SchemaExpression] = (index | schemaFormula)
      def index: Parser[IntegerTerm] = (sum | intConst | intVar | succ  )
      def intConst: Parser[IntegerTerm] = (intZero | intOne | intTwo | intThree)
      def intOne :  Parser[IntegerTerm] = "1".r ^^ { case x => {  Succ(IntZero())}}
      def intTwo :  Parser[IntegerTerm] = "2".r ^^ { case x => {  Succ(Succ(IntZero()))}}
      def intThree: Parser[IntegerTerm] = "3".r ^^ { case x => {  Succ(Succ(Succ(IntZero())))}}
      def intZero:  Parser[IntegerTerm] = "0".r ^^ { case x => {  IntZero()}
      }

      def sum : Parser[IntegerTerm] = intVar ~ "+" ~ intConst ^^ {case indV ~ "+" ~ indC => {
//        println("\n\nsum")
        indC match {
          case Succ(IntZero()) => Succ(indV)
          case Succ(Succ(IntZero())) => Succ(Succ(indV))
          case Succ(Succ(Succ(IntZero()))) => Succ(Succ(Succ(indV)))
      }}}

      def intVar: Parser[IntVar] = "[ijmnkx]".r ^^ {
        case x => { /*println("\n\nintVar");*/ IntVar(x)}
      }
      def succ: Parser[IntegerTerm] = "s(" ~ intTerm ~ ")" ^^ {
        case "s(" ~ intTerm ~ ")" => Succ(intTerm.asInstanceOf[IntegerTerm])
      }

      def schemaFormula = formula

      def indPred : Parser[SchemaFormula] = """[A-Z]*[a-z]*[0-9]*""".r ~ "(" ~ repsep(index,",") ~ ")" ^^ {
        case x ~ "(" ~ l ~ ")" => {
          if (! mapPredicateToArity.isDefinedAt(x.toString) )
            mapPredicateToArity.put(x.toString, l.size)
          else if (mapPredicateToArity.get(x.toString).get != l.size ) {
            println("\nInput ERROR : Indexed Predicate '"+x.toString+"' should have arity "+mapPredicateToArity.get(x.toString).get+ ", but not "+l.size+" !\n\n")
            throw new Exception("\nInput ERROR : Indexed Predicate '"+x.toString+"' should have arity "+mapPredicateToArity.get(x.toString).get+ ", but not "+l.size+" !\n")
          }
//          println("\n\nIndexedPredicate");

//          val map: MMap[Var, T])
//          val subst: SchemaSubstitution1[SchemaExpression] = new SchemaSubstitution1[SchemaExpression]()
//          val new_ind = subst(ind)
//          val new_map = (subst.map - subst.map.head._1.asInstanceOf[Var]) + Tuple2(subst.map.head._1.asInstanceOf[Var], Pred(new_ind.asInstanceOf[IntegerTerm]) )
//          val new_subst = new SchemaSubstitution1(new_map)

          IndexedPredicate(x, l)
        }
      }


      def define: Parser[Unit]  = indPred ~ ":=" ~ schemaFormula ^^ {
        case indpred ~ ":=" ~ sf => {
          indpred match {
            case IndexedPredicate(f,ls) => {
              defMMap.put(f, Tuple2(ls.asInstanceOf[List[IntegerTerm]],sf.asInstanceOf[SchemaFormula]))
            }
          }
        }
      }


     // nested bigAnd bigOr....           ("""BigAnd""".r | """BigOr""".r)
      def prefix : Parser[Tuple4[Boolean, IntVar, IntegerTerm, IntegerTerm]] = """[BigAnd]*[BigOr]*""".r ~ "(" ~ intVar ~ "=" ~ index ~ ".." ~ index ~ ")" ^^ {
        case "BigAnd" ~ "(" ~ intVar1 ~ "=" ~ ind1 ~ ".." ~ ind2 ~ ")"  => {
          //          println("\n\nprefix\n\n")
          Tuple4(true, intVar1, ind1, ind2)
        }
        case "BigOr" ~ "(" ~ intVar1 ~ "=" ~ ind1 ~ ".." ~ ind2 ~ ")"  => {
          //          println("\n\nprefix\n\n")
          Tuple4(false, intVar1, ind1, ind2)
        }
      }

      def big : Parser[SchemaFormula] = rep1(prefix) ~ schemaFormula ^^ {
        case l ~ schemaFormula  => {
          //          println("Works?")
          l.reverse.foldLeft(schemaFormula.asInstanceOf[SchemaFormula])((res, triple) => {
            if (triple._1)
              BigAnd(triple._2, res, triple._3, triple._4)
            else
              BigOr(triple._2, res, triple._3, triple._4)
          })
        }
      }

      def non_formula: Parser[SchemaExpression] = (abs | variable | constant | var_func | const_func)
      def variable: Parser[SchemaVar] = regex(new Regex("[u-z]" + word))  ^^ {case x => SchemaFactory.createVar(StringSymbol(x), Tindex->Tindex)}
      def constant: Parser[SchemaConst] = regex(new Regex("[a-tA-Z0-9]" + word))  ^^ {case x => SchemaFactory.createConst(StringSymbol(x), Tindex->Tindex) }
      def and: Parser[SchemaFormula] = "(" ~ repsep(formula, "/\\") ~ ")" ^^ { case "(" ~ formulas ~ ")"  => { formulas.tail.foldLeft(formulas.head)((f,res) => And(f, res)) } }
      def or: Parser[SchemaFormula]  = "(" ~ repsep(formula, """\/""" ) ~ ")" ^^ { case "(" ~ formulas ~ ")"  => { formulas.tail.foldLeft(formulas.head)((f,res) => Or(f, res)) } }
      def imp: Parser[SchemaFormula] = "Imp" ~ formula ~ formula ^^ {case "Imp" ~ x ~ y => Imp(x,y)}
      def abs: Parser[SchemaExpression] = "Abs" ~ variable ~ term ^^ {case "Abs" ~ v ~ x => SchemaAbs(v,x).asInstanceOf[SchemaExpression]}
      def neg: Parser[SchemaFormula] = "~" ~ formula ^^ {case "~" ~ x => Neg(x)}
      def atom: Parser[SchemaFormula] = (equality | var_atom | const_atom)
      def forall: Parser[SchemaFormula] = "Forall" ~ variable ~ formula ^^ {case "Forall" ~ v ~ x => AllVar(v,x)}
      def exists: Parser[SchemaFormula] = "Exists" ~ variable ~ formula ^^ {case "Exists" ~ v ~ x => ExVar(v,x)}
      def var_atom: Parser[SchemaFormula] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {
//        println("\n\nvar_atom")
        Atom(SchemaVar(x, FunctionType(To, params map (_.exptype) )), params)
      }}
      def const_atom: Parser[SchemaFormula] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {
//        println("\n\nconst_atom")
        Atom(SchemaConst(x, FunctionType(To, params map (_.exptype) )), params)
      }}
      def equality: Parser[SchemaFormula] = /*eq_infix | */ eq_prefix // infix is problematic in higher order
     //def eq_infix: Parser[SchemaFormula] = term ~ "=" ~ term ^^ {case x ~ "=" ~ y => Equation(x,y)}
      def eq_prefix: Parser[SchemaFormula] = "=" ~ "(" ~ term ~ "," ~ term  ~ ")" ^^ {case "=" ~ "(" ~ x ~ "," ~ y  ~ ")" => Equation(x,y)}
      def var_func: Parser[SchemaExpression] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")"  =>
        Function(SchemaVar(x, FunctionType(Tindex->Tindex, params map (_.exptype))), params)}
     /*def var_func: Parser[SchemaExpression] = (var_func1 | var_funcn)
     def var_func1: Parser[SchemaExpression] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")"  ~ ":" ~ Type ^^ {case x ~ "(" ~ params ~ ")" ~ ":" ~ tp => Function(new VariableStringSymbol(x), params, tp)}
     def var_funcn: Parser[SchemaExpression] = regex(new Regex("[u-z]" + word)) ~ "^" ~ decimalNumber ~ "(" ~ repsep(term,",") ~ ")"  ~ ":" ~ Type ^^ {case x ~ "^" ~ n ~ "(" ~ params ~ ")" ~ ":" ~ tp => genF(n.toInt, SchemaVar(new VariableStringSymbol(x)), params)}
     */

      def const_func: Parser[SchemaExpression] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")"  ^^ {case x ~ "(" ~ params ~ ")"  =>
        Function(SchemaConst(x, FunctionType(Tindex->Tindex, params map (_.exptype))), params)}
      protected def word: String = """[a-zA-Z0-9$_{}]*"""
      protected def symbol: Parser[String] = symbols.r
      def symbols: String = """[\053\055\052\057\0134\0136\074\076\075\0140\0176\077\0100\046\0174\041\043\047\073\0173\0175]+""" // +-*/\^<>=`~?@&|!#{}';



//      def sequent: Parser[Sequent] = formula ~ "|-" ~ formula ^^ { case lf ~ "|-" ~ rf => {
      def sequent: Parser[Sequent] = repsep(formula,",") ~ "|-" ~ repsep(formula,",") ^^ { case lfs ~ "|-" ~ rfs => {
//          println("\n\nSEQUENT")
          Axiom(lfs, rfs).root
        }
      }

      def ax: Parser[LKProof] = "ax(" ~ sequent ~ ")" ^^ {
        case "ax(" ~ sequent ~ ")" => {
//          println("\n\nAXIOM")
          Axiom(sequent)
        }
        case _ => {println("ERROR");Axiom(List(), List())}
      }

      def proof_name : Parser[String] = """[\\]*[a-z]*[0-9]*""".r

      def pLink: Parser[LKProof] = "pLink(" ~ "(" ~ proof_name ~ "," ~ index ~ ")"  ~ sequent ~ ")" ^^ {
        case                       "pLink(" ~ "(" ~ name ~       "," ~   v   ~ ")"  ~ sequent ~ ")" => {
//          println("\n\npLink")
          SchemaProofLinkRule(sequent.toFSequent, name, v::Nil)
        }
      }

      def orR1: Parser[LKProof] = "orR1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orR1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
//          println("\n\norR1")
          OrRight1Rule(map.get(l).get, f1, f2)
        }
      }

      def orR2: Parser[LKProof] = "orR2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orR2(" ~ label ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
//          println("\n\norR2")
          OrRight2Rule(map.get(label).get, f1, f2)
        }
      }

      def orR: Parser[LKProof] = "orR(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orR(" ~ label ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
//          println("\n\norR")
          OrRightRule(map.get(label).get, f1, f2)
        }
      }

      def orL: Parser[LKProof] = "orL(" ~ label.r ~ "," ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orL(" ~ l1 ~ "," ~ l2 ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
//          println("\n\norL")
          OrLeftRule(map.get(l1).get, map.get(l2).get, f1, f2)
        }
      }

      def andR: Parser[LKProof] = "andR(" ~ label.r ~ "," ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andR(" ~ l1 ~ "," ~ l2 ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
//          println("\n\nandR")
//          println("\nerror_buffer = "+error_buffer)
//          println("\n"+map.get(l).get.root.toString)
//          println(map.get(l1).get.root)
//          println("\n\n")
//          println(map.get(l2).get.root)
//          println("\n\n")
          val p = AndRightRule(map.get(l1).get, map.get(l2).get, f1, f2)
//          println(p.root)
          p
        }
      }

      def cut: Parser[LKProof] = "cut(" ~ label.r ~ "," ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "cut(" ~ l1 ~ "," ~ l2 ~ "," ~ f ~ ")" => {
//          println("\n\ncut")
//          println("\nerror_buffer = "+error_buffer)

          CutRule(map.get(l1).get, map.get(l2).get, f)
        }
      }

      def negL: Parser[LKProof] = "negL(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "negL(" ~ label ~ "," ~ formula ~ ")" => {
//          println("\n\nnegL")
          NegLeftRule(map.get(label).get, formula)
        }
        case _ => {
          println("\n\nError!")
          sys.exit(10)
        }
      }

      def negR: Parser[LKProof] = "negR(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "negR(" ~ label ~ "," ~ formula ~ ")" => {
//          println("\n\n"+map.get(label).get.root.toString)
//          println("\n\nnegR")
          NegRightRule(map.get(label).get, formula)
        }
      }

      def weakR: Parser[LKProof] = "weakR(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "weakR(" ~ label ~ "," ~ formula ~ ")" => {
//          println("\n\nweakR")
          WeakeningRightRule(map.get(label).get, formula)
        }
      }

      def weakL: Parser[LKProof] = "weakL(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "weakL(" ~ label ~ "," ~ formula ~ ")" => {
//          println("\n\nweakL")
          WeakeningLeftRule(map.get(label).get, formula)
        }
      }
//      def eqAnd1: Parser[LKProof] = "eqAnd1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
//        case "eqAnd1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
//          AndEquivalenceRule1(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
//        }
//      }

      def andL1: Parser[LKProof] = "andL1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andL1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
//          println("\n\nandL1")
          AndLeft1Rule(map.get(l).get, f1, f2)
        }
      }

      def andL2: Parser[LKProof] = "andL2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andL2(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
//          println("\n\nandL2")
          AndLeft2Rule(map.get(l).get, f1, f2)
        }
      }

      def andL: Parser[LKProof] = "andL(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andL(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
//          println("\n\nandL")
//          println("\nerror_buffer = "+error_buffer)
//          println("\n"+map.get(l).get.root.toString)
          val p = AndLeftRule(map.get(l).get, f1, f2)
              p
//          val and = And(f1,f2)
//          val aux = p.root.antecedent.tail.head.formula
//          println("\np   = "+aux)
//          println("\nand = "+and)
//          println("\n\n"+aux.syntaxEquals(and))
//          println("\nf1 = "+f1)
//          var res = p
//          f1 match {
//            case BigAnd(ind,f,lb,ub) => {
//              println("ERROR 5")
////              sys.exit(1)
//              res = AndEquivalenceRule1(p, and.asInstanceOf[SchemaFormula], BigAnd(ind,f,lb,Succ(ub)).asInstanceOf[SchemaFormula])
//              println("\n\nres = "+res.root.antecedent.head.formula)
////              return res
//              res
//            }
//            case _ => {
//              println("ERROR 3")
////              sys.exit(1)
//              res
//            }
//          }
//          println("ERROR 2")
//          res
//              sys.exit(1)
        }
      }

      def andEqR1: Parser[LKProof] = "andEqR1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqR1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndRightEquivalenceRule1(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
        }
      }

      def andEqR2: Parser[LKProof] = "andEqR2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqR2(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndRightEquivalenceRule2(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
        }
      }

      def andEqR3: Parser[LKProof] = "andEqR3(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqR3(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndRightEquivalenceRule3(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
        }
      }

      def andEqL1: Parser[LKProof] = "andEqL1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqL1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndLeftEquivalenceRule1(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
        }
      }

      def andEqL2: Parser[LKProof] = "andEqL2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqL2(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndLeftEquivalenceRule2(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
        }
      }

      def andEqL3: Parser[LKProof] = "andEqL3(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqL3(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndLeftEquivalenceRule3(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
        }
      }

      def orEqR1: Parser[LKProof] = "orEqR1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orEqR1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          OrRightEquivalenceRule1(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
        }
      }

      def orEqR2: Parser[LKProof] = "andEqR2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqR2(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          OrRightEquivalenceRule2(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
        }
      }

      def orEqR3: Parser[LKProof] = "orEqR3(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orEqR3(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          OrRightEquivalenceRule3(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
        }
      }

      def orEqL1: Parser[LKProof] = "orEqL1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orEqL1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          OrLeftEquivalenceRule1(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
        }
      }

      def orEqL2: Parser[LKProof] = "andEqL2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqL2(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          OrLeftEquivalenceRule2(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
        }
      }

      def orEqL3: Parser[LKProof] = "orEqL3(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orEqL3(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          OrLeftEquivalenceRule3(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
        }
      }

      def contrL: Parser[LKProof] = "contrL(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "contrL(" ~ l ~ "," ~ f ~ ")" => {
//          println("\n\ncontrL")
          ContractionLeftRule(map.get(l).get, f)
        }
      }

      def contrR: Parser[LKProof] = "contrR(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "contrR(" ~ l ~ "," ~ f ~ ")" => {
//          println("\n\ncontrR")
          ContractionRightRule(map.get(l).get, f)
        }
      }

    }
//    println("\n\nnumber of SLK-proofs = "+bigMMap.size)
//    println("\ndefMMapr size = "+defMMap.size)

//    println("\n\n\nlist = "+list)
//    if (!bigMMap.get("chi").get._2.isDefinedAt(plabel)) println("\n\n\nSyntax ERROR after ID : " + error_buffer +"\n\n")
//    val m = bigMMap.get("chi").get._2.get(plabel).get
////    println(m.root.antecedent.head+" |- "+m.root.succedent.head)
//    m
  //  println("\nSchemaProofDB.size = "+SchemaProofDB.size+"\n")
    bigMMap
  }
}

/* Moved to schema.scala in languages package. After checking is everything is
 * fine, delete this from here.

class SchemaSubstitution1[T <: HOLExpression](val map: MMap[Var, T])  {
  import at.logic.language.schema._

  def apply(expression: T): T = expression match {
    case x:IntVar => {
//      println("\nIntVar = "+x)
      map.get(x) match {
        case Some(t) => {
//          println("substituting " + t.toStringSimple + " for " + x.toStringSimple)
          t
        }
        case _ => {
//          println(x + " Error in schema subst 1")
          x.asInstanceOf[T]
        }
      }
    }
    case IndexedPredicate(pointer @ f, l @ ts) => IndexedPredicate(pointer.name.asInstanceOf[ConstantSymbolA], apply(l.head.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
    case BigAnd(v, formula, init, end) => BigAnd(v, formula, apply(init.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(end.asInstanceOf[T]).asInstanceOf[IntegerTerm] ).asInstanceOf[T]
    case BigOr(v, formula, init, end) =>   BigOr(v, formula, apply(init.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(end.asInstanceOf[T]).asInstanceOf[IntegerTerm] ).asInstanceOf[T]
    case Succ(n) => Succ(apply(n.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
    case Or(l @ left, r @ right) => Or(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
    case And(l @ left, r @ right) => And(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
    case Neg(l @ left) => Neg(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
    case Imp(l, r) => Imp(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
    case AllVar(v, f) => AllVar(v, apply(f.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
    case at @ Atom(name, args) => {
      Atom(name, args.map(x => apply(x.asInstanceOf[T]).asInstanceOf[HOLExpression])).asInstanceOf[T]
    }
    case ifo: indexedFOVar => indexedFOVar(ifo.name, apply(ifo.index.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
    case st @ sTerm(name, i, args) => {
      sTerm(name.asInstanceOf[HOLConst], apply(i.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(args.asInstanceOf[T])::Nil).asInstanceOf[T]
    }
    case foTerm(v, arg) => foTerm(v.asInstanceOf[HOLVar], apply(arg.asInstanceOf[T])::Nil).asInstanceOf[T]
    case _ => {
//      println("\n SchemaSubstitution1: case _ => " + expression.toString + " : "+expression.getClass)
      expression
    }
  }

  def apply(fseq: types.FSequent): types.FSequent = {
    FSequent(fseq._1.map(f => apply(f.asInstanceOf[T]).asInstanceOf[SchemaFormula]),fseq._2.map(f => apply(f.asInstanceOf[T]).asInstanceOf[SchemaFormula]))
  }
}
*/


//                    This copy has types. This is why it is kept !
//
//object SHLK {
//  //plabel should return the proof corresponding to this label
//  def parseProof(txt: String, plabel: String): LKProof = {
//    val map = MMap.empty[String, LKProof]
//    lazy val sp = new SimpleSLKParser
//    sp.parseAll(sp.line, txt)
//
//
//    class SimpleSLKParser extends JavaTokenParsers with at.logic.language.lambda.types.Parsers {
//
//      def line: Parser[List[Unit]] = rep(mapping)
//
//      def mapping: Parser[Unit] = label.r ~ "=" ~ proof ^^ {
//        case l ~ "=" ~ p => {
//          println("\nl = "+l)
//          map(l) = p
//        }
//      }
//
//      def proof: Parser[LKProof] = ax | orL | orR1 | orR2 | negL | negR
//      def label: String = """[0-9]*"""
//
//      def term: Parser[HOLExpression] = (non_formula | formula)
//      def formula: Parser[SchemaFormula] = (neg | atom | and | or | imp | forall | exists | variable | constant) ^? {case trm: Formula => trm.asInstanceOf[SchemaFormula]}
//      def non_formula: Parser[HOLExpression] = (abs | variable | constant | var_func | const_func)
//      def variable: Parser[HOLVar] = regex(new Regex("[u-z]" + word)) ~ ":" ~ Type ^^ {case x ~ ":" ~ tp => hol.createVar(new VariableStringSymbol(x), tp).asInstanceOf[HOLVar]}
//      def constant: Parser[HOLConst] = regex(new Regex("[a-tA-Z0-9]" + word)) ~ ":" ~ Type ^^ {case x ~ ":" ~ tp => hol.createVar(new ConstantStringSymbol(x), tp).asInstanceOf[HOLConst]}
//      def and: Parser[SchemaFormula] = "And" ~ formula ~ formula ^^ {case "And" ~ x ~ y => And(x,y)}
//      def or: Parser[SchemaFormula] = "Or" ~ formula ~ formula ^^ {case "Or" ~ x ~ y => Or(x,y)}
//      def imp: Parser[SchemaFormula] = "Imp" ~ formula ~ formula ^^ {case "Imp" ~ x ~ y => Imp(x,y)}
//      def abs: Parser[HOLExpression] = "Abs" ~ variable ~ term ^^ {case "Abs" ~ v ~ x => Abs(v,x).asInstanceOf[HOLExpression]}
//      def neg: Parser[SchemaFormula] = "Neg" ~ formula ^^ {case "Neg" ~ x => Neg(x)}
//      def atom: Parser[SchemaFormula] = (equality | var_atom | const_atom)
//      def forall: Parser[SchemaFormula] = "Forall" ~ variable ~ formula ^^ {case "Forall" ~ v ~ x => AllVar(v,x)}
//      def exists: Parser[SchemaFormula] = "Exists" ~ variable ~ formula ^^ {case "Exists" ~ v ~ x => ExVar(v,x)}
//      def var_atom: Parser[SchemaFormula] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Atom(new VariableStringSymbol(x), params)}
//      def const_atom: Parser[SchemaFormula] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Atom(new ConstantStringSymbol(x), params)}
//      def equality: Parser[SchemaFormula] = /*eq_infix | */ eq_prefix // infix is problematic in higher order
//     //def eq_infix: Parser[SchemaFormula] = term ~ "=" ~ term ^^ {case x ~ "=" ~ y => Equation(x,y)}
//      def eq_prefix: Parser[SchemaFormula] = "=" ~ "(" ~ term ~ "," ~ term  ~ ")" ^^ {case "=" ~ "(" ~ x ~ "," ~ y  ~ ")" => Equation(x,y)}
//      def var_func: Parser[HOLExpression] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")"  ~ ":" ~ Type ^^ {case x ~ "(" ~ params ~ ")" ~ ":" ~ tp => Function(new VariableStringSymbol(x), params, tp)}
//     /*def var_func: Parser[HOLExpression] = (var_func1 | var_funcn)
//     def var_func1: Parser[HOLExpression] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")"  ~ ":" ~ Type ^^ {case x ~ "(" ~ params ~ ")" ~ ":" ~ tp => Function(new VariableStringSymbol(x), params, tp)}
//     def var_funcn: Parser[HOLExpression] = regex(new Regex("[u-z]" + word)) ~ "^" ~ decimalNumber ~ "(" ~ repsep(term,",") ~ ")"  ~ ":" ~ Type ^^ {case x ~ "^" ~ n ~ "(" ~ params ~ ")" ~ ":" ~ tp => genF(n.toInt, HOLVar(new VariableStringSymbol(x)), params)}
//     */
//
//      def const_func: Parser[HOLExpression] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ~ ":" ~ Type ^^ {case x ~ "(" ~ params ~ ")" ~ ":" ~ tp  => Function(new ConstantStringSymbol(x), params, tp)}
//      protected def word: String = """[a-zA-Z0-9$_{}]*"""
//      protected def symbol: Parser[String] = symbols.r
//      def symbols: String = """[\053\055\052\057\0134\0136\074\076\075\0140\0176\077\0100\046\0174\041\043\047\073\0173\0175]+""" // +-*/\^<>=`~?@&|!#{}';
//
//      def sequent: Parser[Sequent] = formula ~ "|-" ~ formula ^^ { case lf ~ "|-" ~ rf => {
//          println("\n\nSEQUENT")
//          Axiom(lf::Nil, rf::Nil).root
//        }
//      }
//
//      def orR1: Parser[LKProof] = "orR1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
//        case "orR1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => OrRight1Rule(map.get(l).get, f1, f2)
//      }
//
//      def orR2: Parser[LKProof] = "orR2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
//        case "orR2(" ~ label ~ "," ~ f1 ~ "," ~ f2 ~ ")" => OrRight2Rule(map.get(label).get, f1, f2)
//      }
//
//      def orL: Parser[LKProof] = "orL(" ~ label.r ~ "," ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
//        case "orL(" ~ l1 ~ "," ~ l2 ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
//          println("\n\nOR-Left")
//          OrLeftRule(map.get(l1).get, map.get(l2).get, f1, f2)
//        }
//      }
//
//      def negL: Parser[LKProof] = "negL(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
//        case "negL(" ~ label ~ "," ~ formula ~ ")" => {
//          println("\n\nNEG-Left")
//          NegLeftRule(map.get(label).get, formula)
//        }
//        case _ => {
//          println("\n\nError!")
//          sys.exit(10)
//        }
//      }
//
//      def negR: Parser[LKProof] = "negR(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
//        case "negR(" ~ label ~ "," ~ formula ~ ")" => NegRightRule(map.get(label).get, formula)
//      }
//
//      def ax: Parser[LKProof] = "ax(" ~ sequent ~ ")" ^^ {
//        case "ax(" ~ sequent ~ ")" => {
//          println("\n\nAXIOM")
//          Axiom(sequent)
//        }
//      }
//
//    }
//    println("\n\n\nsize = "+map.size)
//    val m = map.get(plabel).get
////    println(m.root.antecedent.head+" |- "+m.root.succedent.head)
//    m
//
//  }
//}

