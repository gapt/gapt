package at.logic.parsing.language.simple

import at.logic.calculi.lk.macroRules._
import at.logic.calculi.slk._
import at.logic.language.schema.{SchemaFormula, BigAnd, BigOr, IntVar, IntegerTerm, IndexedPredicate, Succ, IntZero, Neg => SNeg}
import at.logic.calculi.lk.base.{Sequent, FSequent, LKProof}
import at.logic.calculi.lk.propositionalRules._
import scala.util.parsing.combinator._
import scala.util.matching.Regex
import at.logic.parsing.language.HOLParser
import at.logic.language.hol._
import at.logic.language.hol.Definitions._
import at.logic.language.hol.ImplicitConverters._
import at.logic.language.lambda.types.TA
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import collection.mutable.Map
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.types._


object SHLK {
  //plabel should return the proof corresponding to this label
  def parseProof(txt: String, plabel: String): LKProof = {
    val map = Map.empty[String, LKProof]
    lazy val sp = new SimpleSLKParser
    sp.parseAll(sp.line, txt)


    class SimpleSLKParser extends JavaTokenParsers with at.logic.language.lambda.types.Parsers {

      def line: Parser[List[Unit]] = rep(mapping)

      def mapping: Parser[Unit] = label.r ~ ":" ~ proof ^^ {
        case l ~ ":" ~ p => {
          println("\nl = "+l)
          map(l) = p
        }
      }

      def proof: Parser[LKProof] = ax | orL | orR1 | orR2 | negL | negR | cut | pLink | andL
      def label: String = """[0-9]*"""

      def term: Parser[HOLExpression] = (non_formula | formula)
      def formula: Parser[HOLFormula] = (neg | bigAnd | bigOr | indPred | and | or | imp | forall | exists | variable | constant) ^? {case trm: Formula => trm.asInstanceOf[HOLFormula]}

      def intTerm: Parser[HOLExpression] = (index | schemaFormula)
      def index: Parser[IntegerTerm] = (sum | intConst | intVar | succ  )
      def intConst: Parser[IntegerTerm] = (intZero | intOne | intTwo | intThree)
      def intOne :  Parser[IntegerTerm] = "1".r ^^ { case x => { println("\n\nintZero");Succ(IntZero())}}
      def intTwo :  Parser[IntegerTerm] = "2".r ^^ { case x => { println("\n\nintZero");Succ(Succ(IntZero()))}}
      def intThree: Parser[IntegerTerm] = "3".r ^^ { case x => { println("\n\nintZero");Succ(Succ(Succ(IntZero())))}}
      def intZero:  Parser[IntegerTerm] = "0".r ^^ { case x => { println("\n\nintZero");IntZero()}
      }
      def sum : Parser[IntegerTerm] = intVar ~ "+" ~ intConst ^^ {case indV ~ "+" ~ indC => {
        println("\n\nsum")
        indC match {
          case Succ(IntZero()) => Succ(indV)
          case Succ(Succ(IntZero())) => Succ(Succ(indV))
          case Succ(Succ(Succ(IntZero()))) => Succ(Succ(Succ(indV)))
      }}}
      def intVar: Parser[IntVar] = "[i,j,m,n,k]".r ^^ {
        case x => { println("\n\nintVar"); IntVar(new VariableStringSymbol(x))}
      }
      def succ: Parser[IntegerTerm] = "s(" ~ intTerm ~ ")" ^^ {
        case "s(" ~ intTerm ~ ")" => Succ(intTerm.asInstanceOf[IntegerTerm])
      }
      def schemaFormula = formula
      def indPred : Parser[HOLFormula] = regex(new Regex("[A-Z0-9]")) ~ "(" ~ index ~ ")" ^^ {
        case x ~ "(" ~ index ~ ")" => { println("\n\nIndexedPredicate"); IndexedPredicate(new ConstantStringSymbol(x), index) }
      }

      def bigAnd : Parser[HOLFormula] = "BigAnd" ~ "(" ~ intVar ~ "," ~ index ~ "," ~ index ~ "," ~ schemaFormula ~ ")" ^^ {
        case "BigAnd" ~ "(" ~ intVar1 ~ "," ~ ind1 ~ "," ~ ind2 ~ "," ~ schemaFormula ~ ")"  => {
          println("\n\nBigAnd\n\n")
          BigAnd(intVar1, schemaFormula.asInstanceOf[SchemaFormula], ind1, ind2)
        }
      }

      def bigOr : Parser[HOLFormula] = "BigOr" ~ "(" ~ intVar ~ "," ~ index ~ "," ~ index ~ "," ~ schemaFormula ~ ")" ^^ {
        case "BigOr" ~ "(" ~ intVar ~ "," ~ ind1 ~ "," ~ ind2 ~ "," ~ schemaFormula ~ ")"  => {
          println("\n\nBigOr\n\n")
          BigOr(intVar, schemaFormula.asInstanceOf[SchemaFormula], ind1, ind2)
        }
      }

      def non_formula: Parser[HOLExpression] = (abs | variable | constant | var_func | const_func)
      def variable: Parser[HOLVar] = regex(new Regex("[u-z]" + word))  ^^ {case x => hol.createVar(new VariableStringSymbol(x), ind->ind).asInstanceOf[HOLVar]}
      def constant: Parser[HOLConst] = regex(new Regex("[a-tA-Z0-9]" + word))  ^^ {case x => hol.createVar(new ConstantStringSymbol(x), ind->ind).asInstanceOf[HOLConst]}
      def and: Parser[HOLFormula] = "And" ~ formula ~ formula ^^ {case "And" ~ x ~ y => And(x,y)}
      def or: Parser[HOLFormula] = "Or" ~ formula ~ formula ^^ {case "Or" ~ x ~ y => Or(x,y)}
      def imp: Parser[HOLFormula] = "Imp" ~ formula ~ formula ^^ {case "Imp" ~ x ~ y => Imp(x,y)}
      def abs: Parser[HOLExpression] = "Abs" ~ variable ~ term ^^ {case "Abs" ~ v ~ x => Abs(v,x).asInstanceOf[HOLExpression]}
      def neg: Parser[HOLFormula] = "Neg" ~ formula ^^ {case "Neg" ~ x => Neg(x)}
      def atom: Parser[HOLFormula] = (equality | var_atom | const_atom)
      def forall: Parser[HOLFormula] = "Forall" ~ variable ~ formula ^^ {case "Forall" ~ v ~ x => AllVar(v,x)}
      def exists: Parser[HOLFormula] = "Exists" ~ variable ~ formula ^^ {case "Exists" ~ v ~ x => ExVar(v,x)}
      def var_atom: Parser[HOLFormula] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {
        println("\n\nvar_atom")
        Atom(new VariableStringSymbol(x), params)
      }}
      def const_atom: Parser[HOLFormula] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {
        println("\n\nconst_atom")
        Atom(new ConstantStringSymbol(x), params)
      }}
      def equality: Parser[HOLFormula] = /*eq_infix | */ eq_prefix // infix is problematic in higher order
     //def eq_infix: Parser[HOLFormula] = term ~ "=" ~ term ^^ {case x ~ "=" ~ y => Equation(x,y)}
      def eq_prefix: Parser[HOLFormula] = "=" ~ "(" ~ term ~ "," ~ term  ~ ")" ^^ {case "=" ~ "(" ~ x ~ "," ~ y  ~ ")" => Equation(x,y)}
      def var_func: Parser[HOLExpression] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")"  => Function(new VariableStringSymbol(x), params, ind->ind)}
     /*def var_func: Parser[HOLExpression] = (var_func1 | var_funcn)
     def var_func1: Parser[HOLExpression] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")"  ~ ":" ~ Type ^^ {case x ~ "(" ~ params ~ ")" ~ ":" ~ tp => Function(new VariableStringSymbol(x), params, tp)}
     def var_funcn: Parser[HOLExpression] = regex(new Regex("[u-z]" + word)) ~ "^" ~ decimalNumber ~ "(" ~ repsep(term,",") ~ ")"  ~ ":" ~ Type ^^ {case x ~ "^" ~ n ~ "(" ~ params ~ ")" ~ ":" ~ tp => genF(n.toInt, HOLVar(new VariableStringSymbol(x)), params)}
     */

      def const_func: Parser[HOLExpression] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")"  ^^ {case x ~ "(" ~ params ~ ")"  => Function(new ConstantStringSymbol(x), params, ind->ind)}
      protected def word: String = """[a-zA-Z0-9$_{}]*"""
      protected def symbol: Parser[String] = symbols.r
      def symbols: String = """[\053\055\052\057\0134\0136\074\076\075\0140\0176\077\0100\046\0174\041\043\047\073\0173\0175]+""" // +-*/\^<>=`~?@&|!#{}';



//      def sequent: Parser[Sequent] = formula ~ "|-" ~ formula ^^ { case lf ~ "|-" ~ rf => {
      def sequent: Parser[Sequent] = repsep(formula,",") ~ "|-" ~ repsep(formula,",") ^^ { case lfs ~ "|-" ~ rfs => {
          println("\n\nSEQUENT")
          Axiom(lfs, rfs).root
        }
      }

      def ax: Parser[LKProof] = "ax(" ~ sequent ~ ")" ^^ {
        case "ax(" ~ sequent ~ ")" => {
          println("\n\nAXIOM")
          Axiom(sequent)
        }
        case _ => {println("ERROR");Axiom(List(), List())}
      }

      def proof_name : Parser[String] = "psi".r

      def pLink: Parser[LKProof] = "pLink(" ~ "(" ~ proof_name ~ "," ~ index ~ ")" ~ "," ~ sequent ~ ")" ^^ {
        case                       "pLink(" ~ "(" ~ name ~ "," ~  v  ~ ")" ~ "," ~ sequent ~ ")" => {
          println("\n\nPROOF-LINK")
          SchemaProofLinkRule(sequent.toFSequent(), name, v::Nil)
        }
        case _ => {println("ERROR 33");Axiom(List(), List())}
      }

      def orR1: Parser[LKProof] = "orR1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orR1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => OrRight1Rule(map.get(l).get, f1, f2)
      }

      def orR2: Parser[LKProof] = "orR2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orR2(" ~ label ~ "," ~ f1 ~ "," ~ f2 ~ ")" => OrRight2Rule(map.get(label).get, f1, f2)
      }

      def orL: Parser[LKProof] = "orL(" ~ label.r ~ "," ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orL(" ~ l1 ~ "," ~ l2 ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          println("\n\nOR-Left")
          OrLeftRule(map.get(l1).get, map.get(l2).get, f1, f2)
        }
      }

      def cut: Parser[LKProof] = "cut(" ~ label.r ~ "," ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "cut(" ~ l1 ~ "," ~ l2 ~ "," ~ f ~ ")" => {
          println("\n\ncut")
          CutRule(map.get(l1).get, map.get(l2).get, f)
        }
      }

      def negL: Parser[LKProof] = "negL(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "negL(" ~ label ~ "," ~ formula ~ ")" => {
          println("\n\nNEG-Left")
          NegLeftRule(map.get(label).get, formula)
        }
        case _ => {
          println("\n\nError!")
          sys.exit(10)
        }
      }

      def negR: Parser[LKProof] = "negR(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "negR(" ~ label ~ "," ~ formula ~ ")" => {
          println("\n\nnegL")
          NegRightRule(map.get(label).get, formula)
        }
      }

//      def eqAnd1: Parser[LKProof] = "eqAnd1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
//        case "eqAnd1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
//          AndEquivalenceRule1(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
//        }
//      }
//
      def andL: Parser[LKProof] = "andL(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andL(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          println("\n\nandL")
          val p = AndLeftRule(map.get(l).get, f1, f2)

          val and = And(f1,f2)
          val aux = p.root.antecedent.tail.head.formula
          println("\np   = "+aux)
          println("\nand = "+and)
          println("\n\n"+aux.syntaxEquals(and))
          println("\nf1 = "+f1)
          var res = p
          f1 match {
            case BigAnd(ind,f,lb,ub) => {
              println("ERROR 5")
//              sys.exit(1)
              res = AndEquivalenceRule1(p, and.asInstanceOf[SchemaFormula], BigAnd(ind,f,lb,Succ(ub)).asInstanceOf[SchemaFormula])
              println("\n\nres = "+res.root.antecedent.head.formula)
//              return res
              res
            }
            case _ => {
              println("ERROR 3")
//              sys.exit(1)
              res
            }
          }
          println("ERROR 2")
          res
//              sys.exit(1)
        }
      }


    }
    println("\n\n\nsize = "+map.size)
    val m = map.get(plabel).get
//    println(m.root.antecedent.head+" |- "+m.root.succedent.head)
    m

  }
}


//
//object SHLK {
//  //plabel should return the proof corresponding to this label
//  def parseProof(txt: String, plabel: String): LKProof = {
//    val map = Map.empty[String, LKProof]
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
//      def formula: Parser[HOLFormula] = (neg | atom | and | or | imp | forall | exists | variable | constant) ^? {case trm: Formula => trm.asInstanceOf[HOLFormula]}
//      def non_formula: Parser[HOLExpression] = (abs | variable | constant | var_func | const_func)
//      def variable: Parser[HOLVar] = regex(new Regex("[u-z]" + word)) ~ ":" ~ Type ^^ {case x ~ ":" ~ tp => hol.createVar(new VariableStringSymbol(x), tp).asInstanceOf[HOLVar]}
//      def constant: Parser[HOLConst] = regex(new Regex("[a-tA-Z0-9]" + word)) ~ ":" ~ Type ^^ {case x ~ ":" ~ tp => hol.createVar(new ConstantStringSymbol(x), tp).asInstanceOf[HOLConst]}
//      def and: Parser[HOLFormula] = "And" ~ formula ~ formula ^^ {case "And" ~ x ~ y => And(x,y)}
//      def or: Parser[HOLFormula] = "Or" ~ formula ~ formula ^^ {case "Or" ~ x ~ y => Or(x,y)}
//      def imp: Parser[HOLFormula] = "Imp" ~ formula ~ formula ^^ {case "Imp" ~ x ~ y => Imp(x,y)}
//      def abs: Parser[HOLExpression] = "Abs" ~ variable ~ term ^^ {case "Abs" ~ v ~ x => Abs(v,x).asInstanceOf[HOLExpression]}
//      def neg: Parser[HOLFormula] = "Neg" ~ formula ^^ {case "Neg" ~ x => Neg(x)}
//      def atom: Parser[HOLFormula] = (equality | var_atom | const_atom)
//      def forall: Parser[HOLFormula] = "Forall" ~ variable ~ formula ^^ {case "Forall" ~ v ~ x => AllVar(v,x)}
//      def exists: Parser[HOLFormula] = "Exists" ~ variable ~ formula ^^ {case "Exists" ~ v ~ x => ExVar(v,x)}
//      def var_atom: Parser[HOLFormula] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Atom(new VariableStringSymbol(x), params)}
//      def const_atom: Parser[HOLFormula] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => Atom(new ConstantStringSymbol(x), params)}
//      def equality: Parser[HOLFormula] = /*eq_infix | */ eq_prefix // infix is problematic in higher order
//     //def eq_infix: Parser[HOLFormula] = term ~ "=" ~ term ^^ {case x ~ "=" ~ y => Equation(x,y)}
//      def eq_prefix: Parser[HOLFormula] = "=" ~ "(" ~ term ~ "," ~ term  ~ ")" ^^ {case "=" ~ "(" ~ x ~ "," ~ y  ~ ")" => Equation(x,y)}
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