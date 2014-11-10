package at.logic.algorithms.shlk

/**
  * Please move this file to parsing!
  */

//import at.logic.calculi.lk.macroRules._
import at.logic.algorithms.lk._
import at.logic.calculi.slk._
import at.logic.calculi.lk.base.{ Sequent, LKProof}
import at.logic.calculi.lk._
import scala.util.parsing.combinator._
import scala.util.matching.Regex
//import at.logic.language.hol._
import at.logic.language.schema._
//import at.logic.language.lambda.typedLambdaCalculus._
import collection.mutable.{Map => MMap}
import at.logic.language.lambda.types._
import java.io.InputStreamReader
import at.logic.language.lambda.symbols._
//import at.logic.calculi.lk.quantificationRules._
//import at.logic.language.hol.And
//import at.logic.language.hol.Or
//import at.logic.language.hol.logicSymbols.StringSymbol
//import at.logic.language.hol.Imp
//import at.logic.language.hol.Neg
//import at.logic.language.lambda.symbols.VariableStringSymbol

object SCHOLParser {

  def parseProofs(input: InputStreamReader): List[(String, LKProof)] = {
    val m = SCHOLParser.parseProof(input)
    m.foldLeft(List.empty[(String, LKProof)])((res, pair) => (pair._1, pair._2._1.get("root").get) :: (pair._1, pair._2._2.get("root").get) :: res)
  }

  //--------------------------------- parse SLK proof -----------------------


  def parseProofFlat(txt: InputStreamReader): MMap[String, Tuple2[LKProof, LKProof]] =
  {
    val map = parseProof( txt )
    map.map( pp => {
      val name = pp._1
      val pair = pp._2
      (name, Tuple2(pair._1.get("root").get, pair._2.get("root").get))
    })
  }
  def parseProof(txt: InputStreamReader): MMap[String, Tuple2[MMap[String, LKProof], MMap[String, LKProof]]] = {
    var mapBase = MMap.empty[String, LKProof]
    var mapStep = MMap.empty[String, LKProof]
    var map  = MMap.empty[String, LKProof]
    var baseORstep: Int = 1
    SchemaProofDB.clear
    var error_buffer = ""
    //    lazy val sp2 = new ParserTxt
    //    sp2.parseAll(sp2.line, txt)
    val bigMMap = MMap.empty[String, Tuple2[MMap[String, LKProof], MMap[String, LKProof]]]
   // val mapPredicateToArity = MMap.empty[String, Int]
    dbTRS.clear
    lazy val sp = new SimpleSCHOLParser
    sp.parseAll(sp.slkProofs, txt) match {
      case sp.Success(result, input) => {}
      case x: AnyRef => throw new Exception(x.toString)
    }


    class SimpleSCHOLParser extends JavaTokenParsers with at.logic.language.lambda.types.Parsers {
      def line: Parser[List[Unit]] = rep(cmappingBase)
      def cmappingBase:Parser[Unit] = ("comment" ~ "\"[\"]*\"") ^^ { case x => () } | mappingBase
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
          if (baseORstep == 1) {
            map = MMap.empty[String, LKProof]
            baseORstep = 2
          }
          map.put(l,p)
          mapStep = map
        }
      }
      def slkProof: Parser[Any] = "proof" ~ """[\\]*[a-z0-9]+""".r ~ "given" ~  "[" ~ repsep(term|IndividualordinalExpressions,",") ~ "]" ~  "proves" ~ sequent ~ "base" ~ "{" ~ line  ~ "}" ~ "step"   ~ "{" ~ rep(mappingStep) ~ "}" ~ rep("""-""".r)  ^^ {
        case                       "proof" ~  str ~ "given" ~ "[" ~ linkparams ~ "]" ~  "proves" ~   seq  ~ "base" ~ "{" ~ line1 ~ "}" ~ "step" ~ "{" ~     line2        ~ "}" ~ procents => {
          bigMMap.put(str, Tuple2(mapBase, mapStep))
          SchemaProofDB.put(new SchemaProof(str, IntVar("k")::Nil, seq.toFSequent, mapBase.get("root").get, mapStep.get("root").get))
          SchemaProofDB.putLinkTerms(str,linkparams)
          mapBase = MMap.empty[String, LKProof]
          mapStep = MMap.empty[String, LKProof]
        }
      }
      def slkProofs: Parser[List[Unit]] =  rep(slkProof) ^^ {case _  => List.empty[Unit]}
      def proof: Parser[LKProof] = ax | orL | orR1 | orR | orR2 | negL | negR | cut | pFOLink | andL | andR| andL1 | andL2 | weakL | weakR | contrL | contrR | andEqR1 | andEqR2 | andEqR3 | orEqR1 | orEqR2 | orEqR3 | andEqL1 | andEqL2 | andEqL3 | orEqL1 | orEqL2 | orEqL3 | allL | exR | exL | exLHyper | allR | allRHyper | allLHyper | exRHyper | impL | impR | termDefL1 | termDefR1 | arrowL | foldL | foldR | arrowR | autoprop
      def label: String = """[0-9()root]*"""
      /////////////////////////////////////////////////////////////////////////////////////////////////////
     // Formulae
      ////////////////////////////////////////////////////////////////////////////////////////////////////
      def formula: Parser[SchemaFormula] =  neg | and | or | imp | forall | forall_hyper  | exists  | exists_hyper | Atoms
      def neg: Parser[SchemaFormula] = "~" ~ formula ^^ {case "~" ~ x => Neg(x)}
      def and: Parser[SchemaFormula] = "(" ~ repsep(formula, "/\\") ~ ")" ^^ { case "(" ~ formulas ~ ")"  => {  And(formulas) } }
      def or: Parser[SchemaFormula]  = "(" ~ repsep(formula, """\/""" ) ~ ")" ^^ { case "(" ~ formulas ~ ")"  => { Or(formulas) } }
      def imp: Parser[SchemaFormula] = "(" ~ formula ~ "->" ~ formula ~ ")" ^^ {case "(" ~ x ~ "->" ~ y ~ ")"=> Imp(x,y)}
      def forall: Parser[SchemaFormula] = "Forall" ~ FOVariable ~ formula ^^ {case "Forall" ~ v ~ x => AllVar(v,x)}
      def forall_hyper: Parser[SchemaFormula] = "ForallHyper" ~ IndividualOrdinalFunctionVar ~ formula ^^ {case "ForallHyper" ~ v ~ x => AllVar(v,x)}
      def exists: Parser[SchemaFormula] = "Exists" ~ FOVariable ~ formula ^^ {case "Exists" ~ v ~ x => ExVar(v,x)}
      def exists_hyper: Parser[SchemaFormula] = "ExistsHyper" ~ IndividualOrdinalFunctionVar ~ formula ^^ {case "ExistsHyper" ~ v ~ x => ExVar(v,x)}
      def Atoms: Parser[SchemaFormula] = inequality | equality | less | sim | lessOrEqual | OrdinalAtom  | BaseAtom
      def inequality: Parser[SchemaFormula] = IndividualSort ~ "\\=" ~ IndividualSort ^^ {case x ~ "\\=" ~ y => Neg(Equation(x,y))}
      def equality: Parser[SchemaFormula] = eq_infix |  eq_prefix
      def eq_infix: Parser[SchemaFormula] = IndividualSort ~ "=" ~ IndividualSort ^^ {case x ~ "=" ~ y => Equation(x,y)}
      def eq_prefix: Parser[SchemaFormula] = "=" ~ "(" ~ IndividualSort ~ "," ~ IndividualSort  ~ ")" ^^ {case "=" ~ "(" ~ x ~ "," ~ y  ~ ")" => Equation(x,y)}
      def less: Parser[SchemaFormula] = IndividualSort ~ "<" ~ IndividualSort ^^ {case x ~ "<" ~ y => lessThan(x,y)}
      def sim: Parser[SchemaFormula]  =   OrdinalSort ~ "~" ~ OrdinalSort  ^^ {case x ~ "~" ~ y => sims(x,y)}
      def lessOrEqual: Parser[SchemaFormula] = IndividualSort ~ "<=" ~ IndividualSort ^^ {case x ~ "<=" ~ y => leq(x,y)}
      def OrdinalAtom: Parser[SchemaFormula] = OrdinalAtomNoArg  |  OrdinalAtomNoOneArg | OrdinalAtomNoTwoArg | OrdinalAtomArg
      def OrdinalAtomArg: Parser[SchemaFormula] = regex(new Regex("[A-Z]+")) ~ "(" ~ OrdinalTerms ~ regex(new Regex(",")) ~ repsep(IndividualSort,",") ~  regex(new Regex(",")) ~ repsep(IndividualordinalExpressions,",") ~ ")" ^^ { case x ~ "(" ~ params1 ~ "," ~ params2 ~ "," ~ params3 ~ ")" => 
        val args = List(params1) ++ params2 ++ params3
        val argstp = args.map(_.exptype)
        Atom(SchemaConst(x, FunctionType(To, argstp)), args)
      }
      def OrdinalAtomNoArg: Parser[SchemaFormula] = regex(new Regex("[A-Z]+")) ~
      "(" ~ OrdinalTerms  ~ ")" ^^ { case x ~ "(" ~ params1 ~ ")" => 
          Atom(SchemaConst(x, ->(To, params1.exptype)), List(params1)) 
      }
      def OrdinalAtomNoTwoArg: Parser[SchemaFormula] = regex(new Regex("[A-Z]+")) ~ "(" ~ OrdinalTerms ~ """,""".r ~ repsep(IndividualordinalExpressions,",")~ ")" ^^ { case x ~ "(" ~ params1 ~ "," ~ params2 ~ ")" => 
        val args = List(params1) ++ params2
        val argstp = args.map(_.exptype)
        Atom(SchemaConst(x, FunctionType(To, argstp)), args)
      }
      def OrdinalAtomNoOneArg: Parser[SchemaFormula] = regex(new Regex("[A-Z]+")) ~ "(" ~ OrdinalTerms ~ """,""".r  ~ repsep(IndividualSort,",") ~ ")" ^^ { case x ~ "(" ~ params1 ~ "," ~ params2 ~  ")" => { 
          val params = List(params1) ++ params2.asInstanceOf[List[SchemaExpression]]
          val head = SchemaConst(x, FunctionType(To, params.map(_.exptype)))
          Atom(head, params) 
        }}
      def BaseAtom: Parser[SchemaFormula] = regex(new Regex("[A-Z]+")) ~ "(" ~ repsep(IndividualSort,",") ~ ")" ^^ { case x ~ "(" ~ params ~ ")" => 
        val argstp = params.map(_.exptype)
        Atom(SchemaConst(x, FunctionType(To, argstp)), params) 
      }
      ////////////////////////////////////////////////////////////////////////////////////////////////////

      /////////////////////////////////////////////////////////////////////////////////////////////////////
      //TERMS
      ////////////////////////////////////////////////////////////////////////////////////////////////////
      def term: Parser[SchemaExpression] = OrdinalSort| IndividualSort
      def OrdinalSort: Parser[SchemaExpression] =  OrdinalFunction | OrdinalTerms
      def IndividualSort: Parser[SchemaExpression] = IndividualFunction  | OrdinalFunctionFarIns |  FOVariable |  constant
      def variable: Parser[SchemaExpression] =   FOVariable | OrdinalFunctionFarIns
      def IndividualordinalExpressions: Parser[SchemaExpression] = IndividualOrdinalFunctionVar | lambdaTerm
      def OrdinalTerms: Parser[SchemaExpression] =  sum | succ | succConsts | numberConsts | intVar
      def VariatedOrdinalTerms: Parser[SchemaExpression] = intVar | succ
      def intConst: Parser[SchemaExpression] = numberConsts | succConsts
      def numberConsts: Parser[SchemaExpression] = """[0-9]+""".r ^^ {case x => {maketogether(augmentString(x).toInt)}}
      def OrdinalFunction: Parser[SchemaExpression] = regex(new Regex("[d]{1}")) ~ "(" ~ repsep(IndividualSort,",") ~ ")"  ^^ {case x ~ "(" ~ params ~ ")"  => 
        Function(SchemaConst(x, FunctionType(Tindex, params.map(_.exptype))), params)
      }
      def sum : Parser[SchemaExpression] = VariatedOrdinalTerms ~ "+" ~ intConst ^^ {case iI ~ "+" ~ iC => { PutPlusTogether(iI,iC)}}
      def intVar: Parser[SchemaExpression] = "k".r ^^ {case x => { SchemaVar(x,Tindex)}}
      def succ: Parser[SchemaExpression] = "s(" ~ VariatedOrdinalTerms ~ ")" ^^ {case "s(" ~ ii ~ ")" => {
        val head = SchemaConst(StringSymbol("schS"), Tindex -> Tindex)
        Function(head, List(ii))}}
      def succConsts: Parser[SchemaExpression] = "s(" ~ intConst ~ ")" ^^ { case "s(" ~ ii ~ ")" => {
        val head = SchemaConst(StringSymbol("schS"), Tindex -> Tindex)
        Function(head, List(ii))
      }}
      def IndividualFunction: Parser[SchemaExpression] = regex(new Regex("[a-z]+")) ~ "(" ~ repsep(IndividualSort,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")"  => {
          val head = SchemaConst(StringSymbol(x), FunctionType(Ti, params.map(_.exptype)))
          Function(head, params)
        }}
      def FOVariable: Parser[SchemaVar] = regex(new Regex("[xyzm]{1}"))  ^^ {case x => SchemaVar(x,Ti)}
      def OrdinalFunctionFarIns: Parser[SchemaExpression] = regex(new Regex("[A-Z]{1}")) ~ "(" ~ OrdinalTerms ~ ")" ^^ {case x ~ "(" ~ ii ~ ")" => { 
          val head = SchemaConst(StringSymbol(x), ii.exptype -> Ti)
          Function(head, List(ii))
        }}
      def constant: Parser[SchemaConst] = regex(new Regex("[c]{1}[a-zA-Z0-9]+"))  ^^ {case x => SchemaConst(StringSymbol(x), Ti)}
      def IndividualOrdinalFunctionVar: Parser[SchemaVar] = regex(new Regex("[A-Z]{1}")) ^^ {case x => SchemaVar(x, Tindex->Ti)}
      def lambdaTerm: Parser[SchemaExpression] = "(" ~ "λ" ~ FOVariable ~ "." ~ IndividualSort ~ ")" ^^ { case "(" ~ "λ" ~ x ~ "." ~ t ~ ")" => SchemaAbs(x, t)}
      ////////////////////////////////////////////////////////////////////////////////////////////////////

      /////////////////////////////////////////////////////////////////////////////////////////////////////
      //RULES
      ////////////////////////////////////////////////////////////////////////////////////////////////////

      def sequent: Parser[Sequent] = repsep(formula,",") ~ "|-" ~ repsep(formula,",") ^^ {
        case lfs ~ "|-" ~ rfs => {
          Axiom(lfs, rfs).root
        }
      }
      def ax: Parser[LKProof] = "ax(" ~ sequent ~ ")" ^^ {
        case "ax(" ~ sequent ~ ")" =>  Axiom(sequent)
        case _ => {println("ERROR");Axiom(List(), List())}
      }
      def pFOLink: Parser[LKProof] = pFOLinkNoArg | pFOLinkNoOneArg  | pFOLinkNoTwoArg | pFOLinkArg
      def pFOLinkNoArg: Parser[LKProof] = "pLink(" ~ "(" ~ """[\\]*[a-z0-9]+""".r ~ "," ~ OrdinalTerms ~ ")" ~ sequent ~ ")" ^^ {
        case "pLink(" ~ "(" ~ name ~ "," ~   l   ~ ")"  ~ sequent ~ ")" => {

          FOSchemaProofLinkRule(sequent.toFSequent, name, List(l).asInstanceOf[List[SchemaExpression]])
        }
      }
      def pFOLinkNoTwoArg: Parser[LKProof] = "pLink(" ~ "(" ~ """[\\]*[a-z0-9]+""".r ~ "," ~ OrdinalTerms ~ "," ~ repsep(IndividualordinalExpressions,",") ~ ")" ~ sequent ~ ")" ^^ {
        case                       "pLink(" ~ "(" ~ name ~       "," ~   l1  ~ "," ~ l2   ~ ")"  ~ sequent ~ ")" => {
          FOSchemaProofLinkRule(sequent.toFSequent, name, List(l1).asInstanceOf[List[SchemaExpression]]++l2.asInstanceOf[List[SchemaExpression]])
        }
      }
      def pFOLinkNoOneArg: Parser[LKProof] = "pLink(" ~ "(" ~ """[\\]*[a-z0-9]+""".r ~ "," ~ OrdinalTerms ~ "," ~  repsep(IndividualSort,",") ~ ")" ~ sequent ~ ")" ^^ {
        case                       "pLink(" ~ "(" ~ name ~       "," ~   l1  ~ "," ~ l2   ~ ")"  ~ sequent ~ ")" => {
          FOSchemaProofLinkRule(sequent.toFSequent, name, List(l1).asInstanceOf[List[SchemaExpression]]++l2)
        }
      }
      def pFOLinkArg: Parser[LKProof] = "pLink(" ~ "(" ~ """[\\]*[a-z0-9]+""".r ~ "," ~ OrdinalTerms ~ "," ~ repsep(IndividualSort,",") ~ "," ~  repsep(IndividualordinalExpressions,",") ~ ")" ~ sequent ~ ")" ^^ {
        case                       "pLink(" ~ "(" ~ name ~       "," ~   l1  ~ "," ~ l2   ~ "," ~ l3 ~ ")"  ~ sequent ~ ")" => {
          FOSchemaProofLinkRule(sequent.toFSequent, name, List(l1).asInstanceOf[List[SchemaExpression]]++l2++l3)
        }
      }
      def orR1: Parser[LKProof] = "orR1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orR1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          //          println("\n\norR1")
          OrRight1Rule(map.get(l).get, f1, f2)
        }
      }
      def orR2: Parser[LKProof] = "orR2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orR2(" ~ label ~ "," ~ f1 ~ "," ~ f2 ~ ")" => OrRight2Rule(map.get(label).get, f1, f2)
      }
      def orR: Parser[LKProof] = "orR(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orR(" ~ label ~ "," ~ f1 ~ "," ~ f2 ~ ")" => OrRightRule(map.get(label).get, f1, f2)
      }
      def orL: Parser[LKProof] = "orL(" ~ label.r ~ "," ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "orL(" ~ l1 ~ "," ~ l2 ~ "," ~ f1 ~ "," ~ f2 ~ ")" => OrLeftRule(map.get(l1).get, map.get(l2).get, f1, f2)
      }
      def andR: Parser[LKProof] = "andR(" ~ label.r ~ "," ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andR(" ~ l1 ~ "," ~ l2 ~ "," ~ f1 ~ "," ~ f2 ~ ")" => AndRightRule(map.get(l1).get, map.get(l2).get, f1, f2)
      }
      def cut: Parser[LKProof] = "cut(" ~ label.r ~ "," ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "cut(" ~ l1 ~ "," ~ l2 ~ "," ~ f ~ ")" => CutRule(map.get(l1).get, map.get(l2).get, f)
      }
      def negL: Parser[LKProof] = "negL(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "negL(" ~ label ~ "," ~ formula ~ ")" => NegLeftRule(map.get(label).get, formula)

        case _ => sys.exit(10)
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
      def andL1: Parser[LKProof] = "andL1(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andL1(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => {
          //          println("\n\nandL1")
          AndLeft1Rule(map.get(l).get, f1, f2)
        }
      }
      def andL2: Parser[LKProof] = "andL2(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andL2(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" => AndLeft2Rule(map.get(l).get, f1, f2)
      }
      def andL: Parser[LKProof] = "andL(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "andL(" ~ l ~ "," ~ f1 ~ "," ~ f2 ~ ")" =>  AndLeftRule(map.get(l).get, f1, f2)

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
          OrRightEquivalenceRule1(map.get(l).get, f1, f2)
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
        case "contrL(" ~ l ~ "," ~ f ~ ")" =>ContractionLeftRule(map.get(l).get, f)
      }
      def contrR: Parser[LKProof] = "contrR(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "contrR(" ~ l ~ "," ~ f ~ ")" => ContractionRightRule(map.get(l).get, f)
      }
      def exR: Parser[LKProof] = "exR(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ "," ~ term ~ ")" ^^ {
        case "exR(" ~ l ~ "," ~ aux ~ "," ~ main ~ "," ~ term ~ ")" => {
          ExistsRightRule(map.get(l).get, aux.asInstanceOf[SchemaFormula], main.asInstanceOf[SchemaFormula], term.asInstanceOf[SchemaExpression])
        }
      }
      def allL: Parser[LKProof] = "allL(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ "," ~ term ~ ")" ^^ {
        case "allL(" ~ l ~ "," ~ aux ~ "," ~ main ~ "," ~ term ~ ")" => {
          ForallLeftRule(map.get(l).get, aux.asInstanceOf[SchemaFormula], main.asInstanceOf[SchemaFormula], term.asInstanceOf[SchemaExpression])
        }
      }
      def allR: Parser[LKProof] = "allR(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ "," ~ (OrdinalFunctionFarIns|FOVariable) ~ ")" ^^ {
        case "allR(" ~ l ~ "," ~ aux ~ "," ~ main ~ "," ~ v ~ ")" => {
          ForallRightRule(map.get(l).get, aux.asInstanceOf[SchemaFormula], main.asInstanceOf[SchemaFormula], v.asInstanceOf[SchemaVar])
        }
      }
      def exL: Parser[LKProof] = "exL(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ "," ~ (OrdinalFunctionFarIns|FOVariable) ~ ")" ^^ {
        case "exL(" ~ l ~ "," ~ aux ~ "," ~ main ~ "," ~ v ~ ")" => {
          ExistsLeftRule(map.get(l).get, aux.asInstanceOf[SchemaFormula], main.asInstanceOf[SchemaFormula], v.asInstanceOf[SchemaVar])
        }
      }
      def exLHyper: Parser[LKProof] = "exLHyper(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ "," ~ IndividualOrdinalFunctionVar ~ ")" ^^ {
        case "exLHyper(" ~ l ~ "," ~ aux ~ "," ~ main ~ "," ~ v ~ ")" => {
          ExistsHyperLeftRule(map.get(l).get, aux.asInstanceOf[SchemaFormula], main.asInstanceOf[SchemaFormula], v.asInstanceOf[SchemaVar])
        }
      }
      def allRHyper: Parser[LKProof] = "allRHyper(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ "," ~ IndividualOrdinalFunctionVar ~ ")" ^^ {
        case "allRHyper(" ~ l ~ "," ~ aux ~ "," ~ main ~ "," ~ v ~ ")" => {
          ForallHyperRightRule(map.get(l).get, aux.asInstanceOf[SchemaFormula], main.asInstanceOf[SchemaFormula], v.asInstanceOf[SchemaVar])
        }
      }
      def exRHyper: Parser[LKProof] = "exRHyper(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ "," ~ IndividualordinalExpressions ~ ")" ^^ {
        case "exRHyper(" ~ l ~ "," ~ aux ~ "," ~ main ~ "," ~ t ~ ")" => {
          ExistsHyperRightRule(map.get(l).get, aux, main, t)
        }
      }
      def allLHyper: Parser[LKProof] = "allLHyper(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ "," ~ IndividualordinalExpressions ~ ")" ^^ {
        case "allLHyper(" ~ l ~ "," ~ aux ~ "," ~ main ~ "," ~ t ~ ")" => {
          ForallHyperLeftRule(map.get(l).get, aux, main, t)
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
      def foldL: Parser[LKProof] = "foldL(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "foldL(" ~ label ~ "," ~ aux ~ "," ~ main ~ ")" => {
          foldLeftRule(map.get(label).get, aux, main)
        }
      }
      def foldR: Parser[LKProof] = "foldR(" ~ label.r ~ "," ~ formula ~ "," ~ formula ~ ")" ^^ {
        case "foldR(" ~ label ~ "," ~ aux ~ "," ~ main ~ ")" => {
          foldRightRule(map.get(label).get, aux, main)
        }
      }
      def arrowL: Parser[LKProof] = "arrowL(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "arrowL(" ~ label ~ "," ~ f1 ~  ")" => {
          trsArrowLeftRule(map.get(label).get, f1)
        }
      }
      def arrowR: Parser[LKProof] = "arrowR(" ~ label.r ~ "," ~ formula ~ ")" ^^ {
        case "arrowR(" ~ label ~ "," ~ f1 ~  ")" => {
          trsArrowRightRule(map.get(label).get, f1)
        }
      }
      def autoprop: Parser[LKProof] = "autoprop(" ~ sequent ~ ")" ^^ {
        case "autoprop(" ~ seq ~ ")" => solve.solvePropositional(seq.toFSequent, throwOnError=true).get
      }
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
    ////////////////////////////////////////////////////////////////////////////////////////////////////
    bigMMap
  }
}
object PutPlusTogether{
  def apply(iI: SchemaExpression, iC: SchemaExpression): SchemaExpression = {
      iC match{
        case SchemaConst(n,t) if n == "0" && t == Tindex => iI
        case Function(n,l,t) if getName(n) == "schS" && t == Tindex => Function(n,List(apply(iI,l.head)))
        case _ =>  throw new Exception("Why?\n" + iC.toString + "\n")
      }
  }
}
object maketogether{
  def apply(i: Int): SchemaExpression = {
    i match{
      case 0 => SchemaConst("0", Tindex)
      case x => {
        val param = apply(x-1)
        val head = SchemaConst("schS", param.exptype -> Tindex)
        Function(head,List(param))
      }
    }
  }
}

object backToInt{
  def apply(i: SchemaExpression): Int = {
    i match{
      case SchemaConst(n,t) if n == "0" && t == Tindex => 0
      case Function(n,l,t) if getName(n) ==  "schS" && t == Tindex =>  1 + apply(l.head)
      case _ => throw new Exception("Why?\n" + i.toString + "\n")
    }
  }
}
