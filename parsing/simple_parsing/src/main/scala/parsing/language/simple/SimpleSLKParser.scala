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

  def parseProofs(input: String): List[(String, LKProof)] = {
//    ("p",parseProof(input, "root"))::Nil
    val m = SHLK.parseProof(input)
    m.foldLeft(List.empty[(String, LKProof)])((res, pair) => (pair._1+"_base", pair._2._1.get("root").get) :: (pair._1+"_step", pair._2._2.get("root").get) :: res)
  }

  //plabel should return the proof corresponding to this label
  def parseProof(txt: String): Map[String, Pair[Map[String, LKProof], Map[String, LKProof]]] = {
    var map = Map.empty[String, LKProof]
    var mapStep = Map.empty[String, LKProof]
    var defMap = Map.empty[SchemaFormula, SchemaFormula]
    var list = List[String]()
    var error_buffer = ""
//    lazy val sp2 = new ParserTxt
//    sp2.parseAll(sp2.line, txt)
    val bigMap = Map.empty[String, Pair[Map[String, LKProof], Map[String, LKProof]]]
    val mapPredicateToArity = Map.empty[String, Int]
    lazy val sp = new SimpleSLKParser

//    var proofName = ""
//    sp.parseAll(sp.line, txt)
    sp.parseAll(sp.slkProofs, txt)


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

      def line: Parser[List[Unit]] = rep(mapping)

      def mapping: Parser[Unit] = label.r ~ ":" ~ proof ^^ {
        case l ~ ":" ~ p => {
          error_buffer = l
          map.put(l,p)
        }
      }

      def mappingStep: Parser[Unit] = label.r ~ ":" ~ proof ^^ {
        case l ~ ":" ~ p => {
          error_buffer = l
          mapStep.put(l,p)
        }
      }

      def name = """[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,_,0,1,2,3,4,5,6,7,8,9]*""".r

      def slkProof: Parser[Unit] = "proof" ~ name ~ "base" ~ "{" ~ line ~ "}" ~ "step" ~ "{" ~ rep(mappingStep) ~ "}"  ^^ {
        case                       "proof" ~  str ~ "base" ~ "{" ~ line1 ~ "}" ~ "step" ~ "{" ~ line2 ~ "}" => {
//          proofName = str
          bigMap.put(str, Pair(map, mapStep))
          map = Map.empty[String, LKProof]
          mapStep = Map.empty[String, LKProof]
          println("\n\nSUCCESSFUL : "+str)
//          List.empty[Unit]
        }
      }

      def abbreviation: Parser[Unit] = define/* ^^ {
        case s ~ d => {
          List.empty[Unit]
        }
      }                                                         */
      def slkProofs: Parser[List[Unit]] =  rep(slkProof)//define  ~ slkProof ^^ {
//         case a ~ s  => {
//          println("\n\n\nslkProofs : number of SLK-proofs = "+bigMap.size)
//          List.empty[Unit]
//        }
//      }
//                                              */

      def proof: Parser[LKProof] = ax | orL | orR1 | orR | orR2 | negL | negR | cut | pLink | andL | andL1 | andL2 | weakL | weakR | andEqR1 | andEqR2 | andEqR3 | orEqR1 | orEqR2 | orEqR3
      def label: String = """[0-9]*[root]*"""

      def term: Parser[HOLExpression] = (non_formula | formula)
      def formula: Parser[HOLFormula] = (neg | big /*| bigAnd | bigOr*/ | and | or | indPred | imp | forall | exists | variable | constant) ^? {case trm: Formula => trm.asInstanceOf[HOLFormula]}

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

      def indPred : Parser[HOLFormula] = """[A-Z]*[a-z]*[0-9]*""".r ~ "(" ~ repsep(index,",") ~ ")" ^^ {
        case x ~ "(" ~ l ~ ")" => {
          if (! mapPredicateToArity.isDefinedAt(x.toString) )
            mapPredicateToArity.put(x.toString, l.size)
          else if (mapPredicateToArity.get(x.toString).get != l.size ) {
            println("\nInput ERROR : Indexed Predicate '"+x.toString+"' should have arity "+mapPredicateToArity.get(x.toString).get+ ", but not "+l.size+" !\n\n")
            throw new Exception("\nInput ERROR : Indexed Predicate '"+x.toString+"' should have arity "+mapPredicateToArity.get(x.toString).get+ ", but not "+l.size+" !\n")
          }
          println("\n\nIndexedPredicate");
          IndexedPredicate(new ConstantStringSymbol(x), l)
        }
      }

      def define: Parser[Unit]  = indPred ~ ":=" ~ schemaFormula ^^ {
        case indpred ~ ":=" ~ f => {
          defMap.put(indpred.asInstanceOf[SchemaFormula], f.asInstanceOf[SchemaFormula])
        }
      }


//      def bigAnd : Parser[HOLFormula] = "BigAnd" ~ "(" ~ intVar ~ "=" ~ index ~ ".." ~ index ~ "," ~ schemaFormula ~ ")" ^^ {
//        case "BigAnd" ~ "(" ~ intVar1 ~ "=" ~ ind1 ~ ".." ~ ind2 ~ "," ~ schemaFormula ~ ")"  => {
//          println("\n\nBigAnd\n\n")
//          BigAnd(intVar1, schemaFormula.asInstanceOf[SchemaFormula], ind1, ind2)
//        }
//      }

     // nested bigAnd bigOr....           ("""BigAnd""".r | """BigOr""".r)
      def prefix : Parser[Tuple3[IntVar, IntegerTerm, IntegerTerm]] = "BigAnd" ~ "(" ~ intVar ~ "=" ~ index ~ ".." ~ index ~ ")" ^^ {
        case "BigAnd" ~ "(" ~ intVar1 ~ "=" ~ ind1 ~ ".." ~ ind2 ~ ")"  => {
          println("\n\nprefix\n\n")
          Tuple3(intVar1, ind1, ind2 )
        }
      }
      def big : Parser[HOLFormula] = rep1(prefix) ~ schemaFormula ^^ {
        case l ~ schemaFormula  => {
          println("Works?")
          l.reverse.foldLeft(schemaFormula.asInstanceOf[SchemaFormula])((res, triple) => BigAnd(triple._1, res, triple._2, triple._3))
//          BigAnd(l.tail.head._1, schemaFormula.asInstanceOf[SchemaFormula], l.tail.head._2, l.tail.head._3)

//          throw new Exception("ERROR in big connective symbol")
//          l.head match {
//            case str ~ "(" ~ intVar1 ~ "=" ~ ind1 ~ ".." ~ ind2 ~ ")" => {
//              if(str == "BigAnd") {
//                println("\n\nBigAnd\n\n")
//                BigAnd(intVar1, schemaFormula.asInstanceOf[SchemaFormula], ind1, ind2)
//              }
//              else if (str == "BigOr") {
//                println("\n\nBigOr\n\n")
//                BigOr(intVar1, schemaFormula.asInstanceOf[SchemaFormula], ind1, ind2)
//              }
//              else {
//                println("\n\nERROR in big connective symbol\n\n")
//                throw new Exception("ERROR in big connective symbol")
//              }
//            }
//          }
        }
      }

//      def bigOr : Parser[HOLFormula] = "BigOr" ~ "(" ~ intVar ~ "," ~ index ~ "," ~ index ~ "," ~ schemaFormula ~ ")" ^^ {
//        case "BigOr" ~ "(" ~ intVar ~ "," ~ ind1 ~ "," ~ ind2 ~ "," ~ schemaFormula ~ ")"  => {
//          println("\n\nBigOr\n\n")
//          BigOr(intVar, schemaFormula.asInstanceOf[SchemaFormula], ind1, ind2)
//        }
//      }

      def non_formula: Parser[HOLExpression] = (abs | variable | constant | var_func | const_func)
      def variable: Parser[HOLVar] = regex(new Regex("[u-z]" + word))  ^^ {case x => hol.createVar(new VariableStringSymbol(x), ind->ind).asInstanceOf[HOLVar]}
      def constant: Parser[HOLConst] = regex(new Regex("[a-tA-Z0-9]" + word))  ^^ {case x => hol.createVar(new ConstantStringSymbol(x), ind->ind).asInstanceOf[HOLConst]}
      def and: Parser[HOLFormula] = "(" ~ formula ~ "/\\" ~ formula ~ ")" ^^ {case "(" ~ x ~ str ~ y ~ ")"  => And(x,y)}
      def or: Parser[HOLFormula]  = "(" ~ formula ~ """\/""" ~ formula ~ ")" ^^ {case "(" ~ x ~ str ~ y ~ ")" => Or(x,y)}
      def imp: Parser[HOLFormula] = "Imp" ~ formula ~ formula ^^ {case "Imp" ~ x ~ y => Imp(x,y)}
      def abs: Parser[HOLExpression] = "Abs" ~ variable ~ term ^^ {case "Abs" ~ v ~ x => Abs(v,x).asInstanceOf[HOLExpression]}
      def neg: Parser[HOLFormula] = "~" ~ formula ^^ {case "~" ~ x => Neg(x)}
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

      def pLink: Parser[LKProof] = "pLink(" ~ "(" ~ proof_name ~ "," ~ index ~ ")"  ~ sequent ~ ")" ^^ {
        case                       "pLink(" ~ "(" ~ name ~       "," ~   v   ~ ")"  ~ sequent ~ ")" => {
          println("\n\nPROOF-LINK")
          SchemaProofLinkRule(sequent.toFSequent(), name, v::Nil)
        }
      }

      def orR1: Parser[LKProof] = "orR1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orR1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => OrRight1Rule(map.get(l).get, f1, f2)
      }

      def orR2: Parser[LKProof] = "orR2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orR2(" ~ label ~ "," ~ f1 ~ "," ~ f2 ~ ")" => OrRight2Rule(map.get(label).get, f1, f2)
      }

      def orR: Parser[LKProof] = "orR(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orR2(" ~ label ~ "," ~ f1 ~ "," ~ f2 ~ ")" => OrRightRule(map.get(label).get, f1, f2)
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

      def weakR: Parser[LKProof] = "weakR(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "weakR(" ~ label ~ "," ~ formula ~ ")" => {
          println("\n\nweakR")
          WeakeningRightRule(map.get(label).get, formula)
        }
      }

      def weakL: Parser[LKProof] = "weakL(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "weakL(" ~ label ~ "," ~ formula ~ ")" => {
          println("\n\nweakL")
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
          AndLeft1Rule(map.get(l).get, f1, f2)
        }
      }

      def andL2: Parser[LKProof] = "andL2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andL2(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndLeft2Rule(map.get(l).get, f1, f2)
        }
      }

      def andL: Parser[LKProof] = "andL(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andL(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          println("\n\nandL")
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

      def ContrL: Parser[LKProof] = "ContrL(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "ContrL(" ~ l ~ "," ~ f ~ ")" => {
          ContractionLeftRule(map.get(l).get, f)
        }
      }

      def ContrR: Parser[LKProof] = "ContrR(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "ContrR(" ~ l ~ "," ~ f ~ ")" => {
          ContractionRightRule(map.get(l).get, f)
        }
      }

    }
    println("\n\n\nnumber of SLK-proof = "+bigMap.size)
    println("\n\n\ndefMapr size = "+defMap.size)

//    println("\n\n\nlist = "+list)
//    if (!bigMap.get("chi").get._2.isDefinedAt(plabel)) println("\n\n\nSyntax ERROR after ID : " + error_buffer +"\n\n")
//    val m = bigMap.get("chi").get._2.get(plabel).get
////    println(m.root.antecedent.head+" |- "+m.root.succedent.head)
//    m
    bigMap

  }
}


//                    This copy has types. This is why it is kept !
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