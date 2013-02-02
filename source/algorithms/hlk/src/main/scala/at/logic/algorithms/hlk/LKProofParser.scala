package at.logic.algorithms.hlk

import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.slk._
import at.logic.language.schema.IndexedPredicate._
import at.logic.calculi.lk.base.{Sequent, LKProof}
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
import collection.mutable.Map
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.types._
import logicSymbols.{ConstantSymbolA, ConstantStringSymbol}
import java.io.InputStreamReader
import at.logic.calculi.lk.quantificationRules._
import at.logic.language.schema.{foVar, dbTRS, foTerm, indexedFOVar, sTerm, SchemaFormula, BigAnd, BigOr, IntVar, IntegerTerm, IndexedPredicate, Succ, IntZero, Neg => SNeg}
import at.logic.algorithms.lk._
import collection.immutable.Stack
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import scala.Tuple4
import at.logic.language.lambda.types.->
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.schema.IntZero
import scala.Tuple2

object LKProofParser {

  def parseProofs(input: InputStreamReader): List[(String, LKProof)] = {
    val m = LKProofParser.parseProof(input)
    m.foldLeft(List.empty[(String, LKProof)])((res, pair) => (pair._1, pair._2._1.get("root").get) :: (pair._1, pair._2._2.get("root").get) :: res)
  }

  //--------------------------------- parse LK proof -----------------------


  def parseProofFlat(txt: InputStreamReader): Map[String, Pair[LKProof, LKProof]] =
  {
    val map = parseProof( txt )
    map.map( pp => {
      val name = pp._1
      val pair = pp._2
      (name, Pair(pair._1.get("root").get, pair._2.get("root").get))
    })
  }

  //plabel should return the proof corresponding to this label
  def parseProof(txt: InputStreamReader): Map[String, Pair[Map[String, LKProof], Map[String, LKProof]]] = {
    var mapBase = Map.empty[String, LKProof]
    var mapStep = Map.empty[String, LKProof]
    var map  = Map.empty[String, LKProof]
    var definitions_map = Map.empty[String, Tuple2[HOLFormula, HOLFormula]]
    SchemaProofDB.clear
    var stackOfProofs: Stack[LKProof] = Stack.empty[LKProof]
    var defMap = Map.empty[HOLConst, Tuple2[List[IntegerTerm] ,SchemaFormula]]
    var error_buffer = ""
    val bigMap = Map.empty[String, Pair[Map[String, LKProof], Map[String, LKProof]]]
    val mapPredicateToArity = Map.empty[String, Int]
    dbTRS.clear
    lazy val sp = new SimpleLKParser

    sp.parseAll(sp.slkProofs, txt) match {
      case sp.Success(result, input) => // println("\n\nSUCCESS parse :) \n")
      case x: AnyRef => // { println("\n\nFAIL parse : \n"+error_buffer); throw new Exception("\n\nFAIL parse :( \n"); }
        throw new Exception(x.toString)
    }


    class SimpleLKParser extends JavaTokenParsers with at.logic.language.lambda.types.Parsers {
      def line: Parser[List[Unit]] = rep(mappingBase)
      def mappingBase: Parser[Unit] = proof ^^ {
        case p => {
//          error_buffer = l
          stackOfProofs = stackOfProofs.push(p)
//          map.put(l,p)
//          mapBase = map
        }
      }

      def name = """(\\)?[a-z0-9_]+""".r

      def definition: Parser[Tuple2[Formula, Formula]] = formula ~ ":=" ~ formula ^^ {
        case f1 ~ ":=" ~ f2 => {
          Tuple2(f1, f2)
        }
      }

      def def_list: Parser[Unit] = "def_list"~":"~ "{" ~ rep(definition) ~ "}" ^^ {
        case "def_list"~":"~ "{" ~ l ~ "}" => {

        }
      }

//      def lkProof: Parser[Unit] = def_list ~ "proof" ~ name ~ "proves" ~ sequent  ~ "{" ~ line ~ "}"  ^^ {
//        case                            dl ~ "proof" ~  str ~ "proves" ~  seq     ~ "{" ~ line1 ~ "}"=> {
//          //          proofName = str

      def lkProof: Parser[Unit] = ("proof" ~> name) ~ ("proves" ~> sequent)  ~ line   ^^ {
        case  str ~  seq ~ line1 => {
          bigMap.put(str, Pair(mapBase, mapStep))
          SchemaProofDB.put(new SchemaProof(str, IntVar(new VariableStringSymbol("k"))::Nil, seq.toFSequent, stackOfProofs.pop2._1, Axiom(Nil,Nil)))
          mapBase = Map.empty[String, LKProof]
        }
      }

      def slkProofs: Parser[List[Unit]] =  rep(trs) ~ rep(define) ~ rep(lkProof) ^^ {
        case a ~ s  => {
          List.empty[Unit]
        }
      }

      def trs: Parser[Unit] = s_term ~ "->" ~ term ~ s_term ~ "->" ~ term ^^ {
        case t1 ~ "->" ~ base ~ t2 ~ "->" ~ step => {
          t1 match {
            case sTerm(func1, i1, arg1) =>
              t2 match {
                case sTerm(func2, i2, arg2) => {
                  dbTRS.add(func1.asInstanceOf[HOLConst], Tuple2(t1, base), Tuple2(t2, step))
                }
              }
          }
        }
      }


      def proof: Parser[LKProof] = ax | orL | orR1 | orR | orR2 | negL | negR | cut | pFOLink | andL | andR| andL1 | andL2 | weakL | weakR | contrL | contrR | andEqR1 | andEqR2 | andEqR3 | orEqR1 | orEqR2 | orEqR3 | andEqL1 | andEqL2 | andEqL3 | orEqL1 | orEqL2 | orEqL3 | allL | allR | impL | impR | autoprop
      def label: String = """[0-9]*[root]*"""

      def term: Parser[HOLExpression] = ( non_formula | formula)
      def formula: Parser[HOLFormula] = (atom | neg | big | and | or | indPred | imp | forall | exists | variable | constant) ^? {case trm: Formula => trm.asInstanceOf[HOLFormula]}
      def intTerm: Parser[HOLExpression] = index //| schemaFormula
      def index: Parser[IntegerTerm] = (sum | intConst | intVar | succ  )
      def intConst: Parser[IntegerTerm] = (intZero | intOne | intTwo | intThree)
      def intOne :  Parser[IntegerTerm] = "1".r ^^ { case x => {  Succ(IntZero())}}
      def intTwo :  Parser[IntegerTerm] = "2".r ^^ { case x => {  Succ(Succ(IntZero()))}}
      def intThree: Parser[IntegerTerm] = "3".r ^^ { case x => {  Succ(Succ(Succ(IntZero())))}}
      def intZero:  Parser[IntegerTerm] = "0".r ^^ { case x => {  IntZero()}
      }

      def sum : Parser[IntegerTerm] = intVar ~ "+" ~ intConst ^^ {case indV ~ "+" ~ indC => {
        indC match {
          case Succ(IntZero()) => Succ(indV)
          case Succ(Succ(IntZero())) => Succ(Succ(indV))
          case Succ(Succ(Succ(IntZero()))) => Succ(Succ(Succ(indV)))
        }}}

      def intVar: Parser[IntVar] = "[i,j,m,n,k,x]".r ^^ { x => IntVar(new VariableStringSymbol(x)) }

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

          IndexedPredicate(new ConstantStringSymbol(x), l)
        }
      }


      def define: Parser[Any]  = indPred ~ ":=" ~ schemaFormula ^^ {
        case indpred ~ ":=" ~ sf => {
          indpred match {
            case IndexedPredicate(f,ls) => {
              defMap.put(f, Tuple2(ls.asInstanceOf[List[IntegerTerm]],sf.asInstanceOf[SchemaFormula]))
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

      def big : Parser[HOLFormula] = rep1(prefix) ~ schemaFormula ^^ {
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
      def non_formula: Parser[HOLExpression] = (fo_term | s_term | indexedVar | abs | variable | constant | var_func | const_func)
      def s_term: Parser[HOLExpression] = "[g,h]".r ~ "(" ~ intTerm ~ "," ~ non_formula ~ ")" ^^ {
        case name ~ "(" ~ i ~ "," ~ args ~ ")" => {
          sTerm(name, i, args::Nil)
        }
      }
      def fo_term: Parser[HOLExpression] = "[f]".r ~ "(" ~ non_formula ~ ")" ^^ {
        case name ~ "(" ~ arg ~ ")" => {
          foTerm(name, arg::Nil)
        }
      }
      def indexedVar: Parser[HOLVar] = regex(new Regex("[z]")) ~ "(" ~ intTerm ~ ")" ^^ {
        case x ~ "(" ~ index ~ ")" => {
          indexedFOVar(new VariableStringSymbol(x), index.asInstanceOf[IntegerTerm])
        }
      }

      // TODO: a should be a FOConstant
      def FOVariable: Parser[HOLVar] = regex(new Regex("[x,y,a]" + word))  ^^ {case x => foVar(x)}
      def variable: Parser[HOLVar] = (indexedVar | FOVariable)//regex(new Regex("[u-z]" + word))  ^^ {case x => hol.createVar(new VariableStringSymbol(x), i->i).asInstanceOf[HOLVar]}
      def constant: Parser[HOLConst] = regex(new Regex("[a-tA-Z0-9]" + word))  ^^ {case x => hol.createVar(new ConstantStringSymbol(x), ind->ind).asInstanceOf[HOLConst]}
      def and: Parser[HOLFormula] = "(" ~ repsep(formula, "/\\") ~ ")" ^^ { case "(" ~ formulas ~ ")"  => { formulas.tail.foldLeft(formulas.head)((f,res) => And(f, res)) } }
      def or: Parser[HOLFormula]  = "(" ~ repsep(formula, """\/""" ) ~ ")" ^^ { case "(" ~ formulas ~ ")"  => { formulas.tail.foldLeft(formulas.head)((f,res) => Or(f, res)) } }
      def imp: Parser[HOLFormula] = "Imp" ~ formula ~ formula ^^ {case "Imp" ~ x ~ y => Imp(x,y)}
      def abs: Parser[HOLExpression] = "Abs" ~ variable ~ term ^^ {case "Abs" ~ v ~ x => Abs(v,x).asInstanceOf[HOLExpression]}
      def neg: Parser[HOLFormula] = "~" ~ formula ^^ {case "~" ~ x => Neg(x)}
      def atom: Parser[HOLFormula] = (equality | var_atom | const_atom)
      def forall: Parser[HOLFormula] = "Forall" ~ variable ~ formula ^^ {case "Forall" ~ v ~ x => AllVar(v,x)}
      def exists: Parser[HOLFormula] = "Exists" ~ variable ~ formula ^^ {case "Exists" ~ v ~ x => ExVar(v,x)}
      def var_atom: Parser[HOLFormula] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {
        //        println("\n\nvar_atom")
        Atom(new VariableStringSymbol(x), params)
      }}

      //      def const_atom: Parser[HOLFormula] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {
      def const_atom: Parser[HOLFormula] = regex(new Regex("P")) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {

        //        println("\n\nconst_atom")
        Atom(new ConstantStringSymbol(x), params)
      }}
      def equality: Parser[HOLFormula] = /*eq_infix | */ eq_prefix // infix is problematic in higher order
      def eq_prefix: Parser[HOLFormula] = "=" ~ "(" ~ term ~ "," ~ term  ~ ")" ^^ {case "=" ~ "(" ~ x ~ "," ~ y  ~ ")" => Equation(x,y)}
      def var_func: Parser[HOLExpression] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")"  => Function(new VariableStringSymbol(x), params, ind->ind)}
      def const_func: Parser[HOLExpression] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")"  ^^ {case x ~ "(" ~ params ~ ")"  => Function(new ConstantStringSymbol(x), params, ind->ind)}
      protected def word: String = """[a-zA-Z0-9$_{}]*"""
      protected def symbol: Parser[String] = symbols.r
      def symbols: String = """[\053\055\052\057\0134\0136\074\076\075\0140\0176\077\0100\046\0174\041\043\047\073\0173\0175]+""" // +-*/\^<>=`~?@&|!#{}';

      //      def sequent: Parser[Sequent] = formula ~ "|-" ~ formula ^^ { case lf ~ "|-" ~ rf => {
      def sequent: Parser[Sequent] = repsep(formula,",") ~ "|-" ~ repsep(formula,",") ^^ {
        case lfs ~ "|-" ~ rfs => {
        //          println("\n\nSEQUENT")
        Axiom(lfs, rfs).root
        }
      }

      def ax: Parser[LKProof] = "ax(" ~ sequent ~ ")" ^^ {
        case "ax(" ~ sequent ~ ")" => {
//                    println("\n\nAXIOM")
          Axiom(sequent)
        }
        case _ => {println("ERROR");Axiom(List(), List())}
      }

      def proof_name : Parser[String] = """[\\]*[a-z]*[0-9]*""".r


      def pFOLink: Parser[LKProof] = "pLink(" ~ "(" ~ proof_name ~ "," ~ index ~ ")"  ~ sequent ~ ")" ^^ {
        case                       "pLink(" ~ "(" ~ name ~       "," ~   v   ~ ")"  ~ sequent ~ ")" => {
          //          println("\n\npLink")
          FOSchemaProofLinkRule(sequent.toFSequent(), name, v::Nil)
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
          val p = AndRightRule(map.get(l1).get, map.get(l2).get, f1, f2)
          p
        }
      }

      def cut: Parser[LKProof] = "cut(" ~ formula ~ ")" ^^ {
        case "cut(" ~ f ~ ")" => {
          val top1 = stackOfProofs.pop2._1
          stackOfProofs = stackOfProofs.pop2._2
          val top2 = stackOfProofs.pop2._1
          stackOfProofs = stackOfProofs.pop2._2
          CutRule(top2, top1, f)
        }
      }

      def negL: Parser[LKProof] = "negL(" ~ formula ~ ")" ^^ {
        case "negL(" ~ formula ~ ")" => {
          val top = stackOfProofs.pop2._1
          stackOfProofs = stackOfProofs.pop2._2
          NegLeftRule(top, formula)
        }
      }

      def negR: Parser[LKProof] = "negR(" ~ formula ~ ")" ^^ {
        case "negR(" ~ formula ~ ")" => {
          val top = stackOfProofs.pop2._1
          stackOfProofs = stackOfProofs.pop2._2
          NegRightRule(top, formula)
        }
      }

      def weakR: Parser[LKProof] = "weakR(" ~ formula ~ ")" ^^ {
        case "weakR(" ~ formula ~ ")" => {
          val top = stackOfProofs.pop2._1
          stackOfProofs = stackOfProofs.pop2._2
          WeakeningRightRule(top, formula)
        }
      }

      def weakL: Parser[LKProof] = "weakL(" ~ formula ~ ")" ^^ {
        case "weakL(" ~ formula ~ ")" => {
          val top = stackOfProofs.pop2._1
          stackOfProofs = stackOfProofs.pop2._2
          WeakeningLeftRule(top, formula)
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
          val p = AndLeftRule(map.get(l).get, f1, f2)
          p
        }
      }

      def andEqR1: Parser[LKProof] = "andEqR1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqR1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndRightEquivalenceRule1(map.get(l).get, f1, f2)
        }
      }

      def andEqR2: Parser[LKProof] = "andEqR2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqR2(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndRightEquivalenceRule2(map.get(l).get, f1, f2)
        }
      }

      def andEqR3: Parser[LKProof] = "andEqR3(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqR3(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndRightEquivalenceRule3(map.get(l).get, f1, f2)
        }
      }

      def andEqL1: Parser[LKProof] = "andEqL1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqL1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndLeftEquivalenceRule1(map.get(l).get, f1, f2)
        }
      }

      def andEqL2: Parser[LKProof] = "andEqL2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqL2(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndLeftEquivalenceRule2(map.get(l).get, f1, f2)
        }
      }

      def andEqL3: Parser[LKProof] = "andEqL3(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andEqL3(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          AndLeftEquivalenceRule3(map.get(l).get, f1, f2)
        }
      }

      def orEqR1: Parser[LKProof] = "orEqR1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orEqR1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          OrRightEquivalenceRule1(map.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
        }
      }

      def orEqR2: Parser[LKProof] = "orEqR2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orEqR2(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
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

      def orEqL2: Parser[LKProof] = "orEqL2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orEqL2(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
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

      def allL: Parser[LKProof] = "allL(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ "," ~ non_formula ~ ")" ^^ {
        case "allL(" ~ l ~ "," ~ aux ~ "," ~ main ~ "," ~ term ~ ")" => {
          ForallLeftRule(map.get(l).get, aux.asInstanceOf[HOLFormula], main.asInstanceOf[HOLFormula], term.asInstanceOf[HOLExpression])
        }
      }

      def allR: Parser[LKProof] = "allR(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ "," ~ (indexedVar|FOVariable) ~ ")" ^^ {
        case "allR(" ~ l ~ "," ~ aux ~ "," ~ main ~ "," ~ v ~ ")" => {
          ForallRightRule(map.get(l).get, aux.asInstanceOf[HOLFormula], main.asInstanceOf[HOLFormula], v.asInstanceOf[HOLVar])
        }
      }

      def impL: Parser[LKProof] = "impL(" ~ label.r ~ "," ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "impL(" ~ l1 ~ "," ~ l2 ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          ImpLeftRule(map.get(l1).get, map.get(l2).get, f1, f2)
        }
      }

      def impR: Parser[LKProof] = "impR(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "impR(" ~ label ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          ImpRightRule(map.get(label).get, f1, f2)
        }
      }

      def autoprop: Parser[LKProof] = "autoprop(" ~ sequent ~ ")" ^^ {
        case "autoprop(" ~ seq ~ ")" => solvePropositional.autoProp(seq.toFSequent())
      }

    }
    bigMap
  }
}


object applyContr {
  def apply(f: HOLFormula, p:LKProof): LKProof = {
    val seq = p.root
    val ant1 = seq.antecedent.filter(fo => fo.formula == f)
    val succ1 = seq.succedent.filter(fo => fo.formula == f)
    var p1: LKProof = p
    if (ant1.size > 1)
      p1 = ContractionLeftRule(p1,f)
    if (succ1.size > 1)
      p1 = ContractionRightRule(p1,f)
    return p1
  }
}