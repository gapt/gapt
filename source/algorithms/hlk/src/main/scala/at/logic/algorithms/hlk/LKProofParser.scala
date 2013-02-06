package at.logic.algorithms.hlk

import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.slk._
import at.logic.language.schema.IndexedPredicate._
import at.logic.calculi.lk.base.{FSequent, Sequent, LKProof}
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
import at.logic.calculi.lk.base.types.FSequent
import collection.mutable
import collection.immutable
import at.logic.parsing.language.xml.ProofDatabase

object LKProofParser {
  def debug(s:String) = { }


  def parseProofs(input: InputStreamReader): List[(String, LKProof)] = {
    val m = LKProofParser.parseProof(input)
    m.proofs
  }

  def parseProofFlat(txt: InputStreamReader): immutable.Map[String, LKProof] =
  {
    val proofdb = parseProof( txt )
    immutable.Map.empty[String, LKProof] ++ (proofdb.proofs)
  }

  //plabel should return the proof corresponding to this label
  def parseProof(txt: InputStreamReader): ProofDatabase = {
    dbTRS.clear
    lazy val sp = new SimpleLKParser with SchemaFormulaParser { def getInput = txt }

    sp.parseAll(sp.hlk_file, txt) match {
      case sp.Success(result, input) =>
        sp.getProofDB
      case x: AnyRef =>
        throw new Exception(x.toString)
    }


  }
}

abstract trait SimpleLKParser extends JavaTokenParsers  {
  import LKProofParser.debug

  //type ProofMap = mutable.HashMap[String,LKProof]

  //maps to prevent passing around lots of parameters
  var stackOfProofs: Stack[LKProof] = Stack.empty[LKProof]
  val proofs  = mutable.Map.empty[String, LKProof]

  def getProofDB : ProofDatabase = {
    new ProofDatabase(Map.empty[HOLExpression,HOLExpression], proofs.toList, Nil, Nil)
  }

  //abstract parsers for formulas
  def term: Parser[HOLExpression];
  def formula: Parser[HOLFormula];
  def non_formula: Parser[HOLExpression];
  def variable: Parser[HOLVar];

  // hardcoded syntax conventions
  val proof_name : Parser[String] = """[\\]*[a-z]*[0-9]*""".r
  val name = """(\\)?[a-z0-9_]+""".r
  val label = """[0-9]*[root]*""".r


  def hlk_file: Parser[List[LKProof]] =  rep(lkProof)

  def line: Parser[List[LKProof]] = rep(proof)


  def lkProof: Parser[LKProof] = ("proof" ~> name) ~ ("proves" ~> sequent)  ~ line   ^^ {
    case  proofname ~  endsequent ~ line => {
      proofs.put(proofname, stackOfProofs.head)
      stackOfProofs.head
    }
  }


  def proof: Parser[LKProof] = (ax | orL | orR1 | orR | orR2 |
                               negL | negR | cut |
                               andL | andR| andL1 | andL2 |
                               weakL | weakR | contrL | contrR |
                               andEqR1 | andEqR2 | andEqR3 |
                               orEqR1 | orEqR2 | orEqR3 |
                               andEqL1 | andEqL2 | andEqL3 |
                               orEqL1 | orEqL2 | orEqL3 |
                               allL | allR | impL | impR |
                               autoprop) ^^ { p => stackOfProofs = stackOfProofs.push(p); p }




  //      def sequent: Parser[Sequent] = formula ~ "|-" ~ formula ^^ { case lf ~ "|-" ~ rf => {
  def sequent: Parser[FSequent] = repsep(formula,",") ~ ":-" ~ repsep(formula,",") ^^ {
    case lfs ~ ":-" ~ rfs => {
      //          println("\n\nSEQUENT")
      FSequent(lfs, rfs)
    }
  }

  /* ========== axiom rules ========================== */

  def ax: Parser[LKProof] = "ax(" ~> sequent <~ ")" ^^ { sequent =>  Axiom(sequent.antecedent, sequent.succedent)  }

  /*
  def pFOLink: Parser[LKProof] = "pLink(" ~ "(" ~ proof_name ~ "," ~ index ~ ")"  ~ sequent ~ ")" ^^ {
    case                       "pLink(" ~ "(" ~ name ~       "," ~   v   ~ ")"  ~ sequent ~ ")" => {
      debug("\n\npLink")
      FOSchemaProofLinkRule(sequent, name, v::Nil)
    }
  }
  */

  /* ========== structural rules ===================== */
  def cut: Parser[LKProof] = "cut(" ~ formula ~ ")" ^^ {
    case "cut(" ~ f ~ ")" => {
      val (top1, stack1) = stackOfProofs.pop2
      stackOfProofs = stack1

      val (top2, stack2) = stackOfProofs.pop2
      stackOfProofs = stack2
      CutRule(top2, top1, f)
    }
  }


  def contrL: Parser[LKProof] = "contrL(" ~ label ~ "," ~ formula ~ ")" ^^ {
    case "contrL(" ~ l ~ "," ~ f ~ ")" => {
      debug("\n\ncontrL")
      ContractionLeftRule(proofs.get(l).get, f)
    }
  }

  def contrR: Parser[LKProof] = "contrR(" ~ label ~ "," ~ formula ~ ")" ^^ {
    case "contrR(" ~ l ~ "," ~ f ~ ")" => {
      debug("\n\ncontrR")
      ContractionRightRule(proofs.get(l).get, f)
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

  /* ================ logical rules ======================= */

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

  def orR1: Parser[LKProof] = "orR1(" ~> label ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l ~ f1  ~ f2 => {
      debug("\n\norR1")
      OrRight1Rule(proofs.get(l).get, f1, f2)
    }
  }

  def orR2: Parser[LKProof] = "orR2("~> label ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l ~ f1 ~ f2 => {
      debug("\n\norR2")
      OrRight2Rule(proofs.get(l).get, f1, f2)
    }
  }

  def orR: Parser[LKProof] = "orR("~> label ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l ~ f1 ~ f2 => {
      debug("\n\norR")
      OrRightRule(proofs.get(l).get, f1, f2)
    }
  }

  def orL: Parser[LKProof] = "orL(" ~> label ~ (","~> label) ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l1 ~ l2  ~ f1 ~ f2 => {
      debug("\n\norL")
      OrLeftRule(proofs.get(l1).get, proofs.get(l2).get, f1, f2)
    }
  }

  def andR: Parser[LKProof] = "andR(" ~> label ~ (","~> label) ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l1 ~ l2 ~ f1 ~ f2 => {
      val p = AndRightRule(proofs.get(l1).get, proofs.get(l2).get, f1, f2)
      p
    }
  }


  def andL1: Parser[LKProof] = "andL1("~> label ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l ~ f1 ~ f2 => {
      debug("\n\nandL1")
      AndLeft1Rule(proofs.get(l).get, f1, f2)
    }
  }

  def andL2: Parser[LKProof] = "andL2("~> label ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l ~ f1 ~ f2 => {
      debug("\n\nandL2")
      AndLeft2Rule(proofs.get(l).get, f1, f2)
    }
  }

  def andL: Parser[LKProof] = "andL("~> label ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l ~ f1 ~ f2 => {
      val p = AndLeftRule(proofs.get(l).get, f1, f2)
      p
    }
  }

  def andEqR1: Parser[LKProof] = "andEqR1("~> label ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l ~ f1 ~ f2 => {
      AndRightEquivalenceRule1(proofs.get(l).get, f1, f2)
    }
  }

  def andEqR2: Parser[LKProof] = "andEqR2("~> label ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l ~ f1 ~ f2 => {
      AndRightEquivalenceRule2(proofs.get(l).get, f1, f2)
    }
  }

  def andEqR3: Parser[LKProof] = "andEqR3("~> label ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l ~ f1 ~ f2 => {
      AndRightEquivalenceRule3(proofs.get(l).get, f1, f2)
    }
  }

  def andEqL1: Parser[LKProof] = "andEqL1("~> label ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l ~ f1 ~ f2 => {
      AndLeftEquivalenceRule1(proofs.get(l).get, f1, f2)
    }
  }

  def andEqL2: Parser[LKProof] = "andEqL2("~> label ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l ~ f1 ~ f2 => {
      AndLeftEquivalenceRule2(proofs.get(l).get, f1, f2)
    }
  }

  def andEqL3: Parser[LKProof] = "andEqL3("~> label ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l ~ f1 ~ f2 => {
      AndLeftEquivalenceRule3(proofs.get(l).get, f1, f2)
    }
  }

  def orEqR1: Parser[LKProof] = "orEqR1("~> label ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l ~ f1 ~ f2 => {
      OrRightEquivalenceRule1(proofs.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
    }
  }

  def orEqR2: Parser[LKProof] = "orEqR2("~> label ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l ~ f1 ~ f2 => {
      OrRightEquivalenceRule2(proofs.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
    }
  }

  def orEqR3: Parser[LKProof] = "orEqR3("~> label ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l ~ f1 ~ f2 => {
      OrRightEquivalenceRule3(proofs.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
    }
  }

  def orEqL1: Parser[LKProof] = "orEqL1("~> label ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l ~ f1 ~ f2 => {
      OrLeftEquivalenceRule1(proofs.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
    }
  }

  def orEqL2: Parser[LKProof] = "orEqL2("~> label ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l ~ f1 ~ f2 => {
      OrLeftEquivalenceRule2(proofs.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
    }
  }

  def orEqL3: Parser[LKProof] = "orEqL3("~> label ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l ~ f1 ~ f2 => {
      OrLeftEquivalenceRule3(proofs.get(l).get, f1.asInstanceOf[SchemaFormula], f2.asInstanceOf[SchemaFormula])
    }
  }


  def impL: Parser[LKProof] = "impL(" ~> label ~ (","~> label) ~ ("," ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case l1 ~ l2 ~ f1 ~ f2  => {
      ImpLeftRule(proofs.get(l1).get, proofs.get(l2).get, f1, f2)
    }
  }

  def impR: Parser[LKProof] = "impR(" ~> label ~ ("," ~> formula) ~ ("," ~> formula <~ ")") ^^ {
    case label ~ f1 ~ f2 => {
      ImpRightRule(proofs.get(label).get, f1, f2)
    }
  }


  def allL: Parser[LKProof] = "allL(" ~> label ~ ("," ~> formula) ~ ("," ~> formula) ~ ("," ~> non_formula) <~ ")" ^^ {
    case l ~ aux ~ main ~ term => {
      ForallLeftRule(proofs.get(l).get, aux, main, term)
    }
  }

  def allR: Parser[LKProof] = "allR(" ~> label ~ ("," ~> formula) ~ ("," ~> formula) ~ ("," ~> (variable)) <~ ")" ^^ {
    case l ~ aux ~ main ~ v  => {
      ForallRightRule(proofs.get(l).get, aux, main, v)
    }
  }

  def exR: Parser[LKProof] = "exR(" ~> label ~ ("," ~> formula) ~ ("," ~> formula) ~ ("," ~> non_formula) <~ ")" ^^ {
    case l ~ aux ~ main ~ term => {
      ExistsRightRule(proofs.get(l).get, aux, main, term)
    }
  }

  def exL: Parser[LKProof] = "exL(" ~> label ~ ("," ~> formula) ~ ("," ~> formula) ~ ("," ~> (variable)) <~ ")" ^^ {
    case l ~ aux ~ main ~ v  => {
      ExistsLeftRule(proofs.get(l).get, aux, main, v)
    }
  }
  def autoprop: Parser[LKProof] = "autoprop(" ~> sequent <~ ")" ^^ { seq  => solvePropositional.autoProp(seq)  }

}


// trying to separate formula parsing from language parsing
trait SchemaFormulaParser extends JavaTokenParsers with HOLParser {
    import LKProofParser.debug

    def goal = term

    val predicate_arities = mutable.Map.empty[String, Int]

    def intConst : Parser[IntegerTerm] = "[0-9]+".r ^^ { x => intToTerm(x.toInt) }
    def intVar: Parser[IntVar] = "[ijmnkx]".r ^^ { x => IntVar(new VariableStringSymbol(x)) }

    def term: Parser[HOLExpression] = ( non_formula | formula)
    def formula: Parser[HOLFormula] = (atom | neg | big | and | or | indPred | imp | forall | exists | variable | constant) ^? {case trm: Formula => trm.asInstanceOf[HOLFormula]}
    def intTerm: Parser[HOLExpression] = index //| schemaFormula
    def index: Parser[IntegerTerm] = (sum | intConst | intVar | succ  )


    def intToTerm(i : Int) : IntegerTerm = {
      require(i >= 0, "Can only process positive integer constants")
      if (i == 0)
        IntZero()
      else
        Succ(intToTerm(i-1))
    }


    private def add(x: IntegerTerm, y:IntegerTerm) : IntegerTerm = y match {
      case IntZero() => x
      case Succ(y_) => add(Succ(x), y_)
      case IntVar(v) => throw new Exception("Sum calculation during parsing requires the second parameter to be ground, encountered: "+y)
      case _ => throw new Exception("Unhandled integer term in sum calculation: "+y)
    }

    private def sum : Parser[IntegerTerm] = intVar ~ ("+" ~> intConst) ^^ {case v ~ c => add(v,c) }

    private def succ: Parser[IntegerTerm] = "s(" ~ intTerm ~ ")" ^^ {
      case "s(" ~ intTerm ~ ")" => Succ(intTerm.asInstanceOf[IntegerTerm])
    }

    def schemaFormula = formula

    def indPred : Parser[HOLFormula] = """[A-Z]*[a-z]*[0-9]*""".r ~ "(" ~ repsep(index,",") ~ ")" ^^ {
      case x ~ "(" ~ l ~ ")" => {
        if (! predicate_arities.isDefinedAt(x.toString) )
          predicate_arities.put(x.toString, l.size)
        else if (predicate_arities.get(x.toString).get != l.size ) {
          println("\nInput ERROR : Indexed Predicate '"+x.toString+"' should have arity "+predicate_arities.get(x.toString).get+ ", but not "+l.size+" !\n\n")
          throw new Exception("\nInput ERROR : Indexed Predicate '"+x.toString+"' should have arity "+predicate_arities.get(x.toString).get+ ", but not "+l.size+" !\n")
        }

        IndexedPredicate(new ConstantStringSymbol(x), l)
      }
    }

    def big : Parser[HOLFormula] = rep1(prefix) ~ schemaFormula ^^ {
      case l ~ schemaFormula  => {
        debug("Works?")
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


    private def fo_term: Parser[HOLExpression] = "[f]".r ~ "(" ~ non_formula ~ ")" ^^ {
      case name ~ "(" ~ arg ~ ")" => {
        foTerm(name, arg::Nil)
      }
    }
    def indexedVar: Parser[HOLVar] = regex(new Regex("[z]")) ~ "(" ~ intTerm ~ ")" ^^ {
      case x ~ "(" ~ index ~ ")" => {
        indexedFOVar(new VariableStringSymbol(x), index.asInstanceOf[IntegerTerm])
      }
    }

    def variable: Parser[HOLVar] = (indexedVar | FOVariable)//regex(new Regex("[u-z]" + word))  ^^ {case x => hol.createVar(new VariableStringSymbol(x), i->i).asInstanceOf[HOLVar]}
    private def FOVariable: Parser[HOLVar] = regex(new Regex("[xya]" + word))  ^^ {case x => foVar(x)}
    private def constant: Parser[HOLConst] = regex(new Regex("[a-tA-Z0-9]" + word))  ^^ {case x => hol.createVar(new ConstantStringSymbol(x), ind->ind).asInstanceOf[HOLConst]}
    private def and: Parser[HOLFormula] = "(" ~ repsep(formula, "/\\") ~ ")" ^^ { case "(" ~ formulas ~ ")"  => { formulas.tail.foldLeft(formulas.head)((f,res) => And(f, res)) } }
    private def or: Parser[HOLFormula]  = "(" ~ repsep(formula, """\/""" ) ~ ")" ^^ { case "(" ~ formulas ~ ")"  => { formulas.tail.foldLeft(formulas.head)((f,res) => Or(f, res)) } }
    private def imp: Parser[HOLFormula] = "Imp" ~ formula ~ formula ^^ {case "Imp" ~ x ~ y => Imp(x,y)}
    private def abs: Parser[HOLExpression] = "Abs" ~ variable ~ term ^^ {case "Abs" ~ v ~ x => Abs(v,x).asInstanceOf[HOLExpression]}
    private def neg: Parser[HOLFormula] = "~" ~ formula ^^ {case "~" ~ x => Neg(x)}
    private def atom: Parser[HOLFormula] = (equality | var_atom | const_atom)
    private def forall: Parser[HOLFormula] = "Forall" ~ variable ~ formula ^^ {case "Forall" ~ v ~ x => AllVar(v,x)}
    private def exists: Parser[HOLFormula] = "Exists" ~ variable ~ formula ^^ {case "Exists" ~ v ~ x => ExVar(v,x)}
    private def var_atom: Parser[HOLFormula] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {
      Atom(new VariableStringSymbol(x), params)
    }}

    //      def const_atom: Parser[HOLFormula] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {
    def const_atom: Parser[HOLFormula] = regex(new Regex("P")) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")" => {

      Atom(new ConstantStringSymbol(x), params)
    }}
    //def equality: Parser[HOLFormula] = eq_infix | eq_prefix // infix is problematic in higher order
    def equality: Parser[HOLFormula] = eq_prefix // infix is problematic in higher order
    def eq_prefix: Parser[HOLFormula] = "=" ~ "(" ~ term ~ "," ~ term  ~ ")" ^^ {case "=" ~ "(" ~ x ~ "," ~ y  ~ ")" => Equation(x,y)}
    def var_func: Parser[HOLExpression] = regex(new Regex("[u-z]" + word)) ~ "(" ~ repsep(term,",") ~ ")" ^^ {case x ~ "(" ~ params ~ ")"  => Function(new VariableStringSymbol(x), params, ind->ind)}
    def const_func: Parser[HOLExpression] = regex(new Regex("["+symbols+"a-tA-Z0-9]" + word)) ~ "(" ~ repsep(term,",") ~ ")"  ^^ {case x ~ "(" ~ params ~ ")"  => Function(new ConstantStringSymbol(x), params, ind->ind)}

    protected def word: String = """[a-zA-Z0-9$_{}]*"""
    protected def symbol: Parser[String] = symbols.r
    def symbols: String = """[\053\055\052\057\0134\0136\074\076\075\0140\0176\077\0100\046\0174\041\043\047\073\0173\0175]+""" // *+-/\^<>=`~?@&|!#{}';

    // nested bigAnd bigOr....           ("""BigAnd""".r | """BigOr""".r)
    def prefix : Parser[Tuple4[Boolean, IntVar, IntegerTerm, IntegerTerm]] = """[BigAnd]*[BigOr]*""".r ~ "(" ~ intVar ~ "=" ~ index ~ ".." ~ index ~ ")" ^^ {
      case "BigAnd" ~ "(" ~ intVar1 ~ "=" ~ ind1 ~ ".." ~ ind2 ~ ")"  => {
        debug("\n\nprefix\n\n")
        Tuple4(true, intVar1, ind1, ind2)
      }
      case "BigOr" ~ "(" ~ intVar1 ~ "=" ~ ind1 ~ ".." ~ ind2 ~ ")"  => {
        debug("\n\nprefix\n\n")
        Tuple4(false, intVar1, ind1, ind2)
      }
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