package at.logic.algorithms.hlk

import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.macroRules._
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
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import scala.Tuple4
import at.logic.language.lambda.types.->
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.schema.IntZero
import at.logic.calculi.lk.base.types.FSequent
import at.logic.parsing.language.xml.ProofDatabase
import at.logic.parsing.language.prover9.Prover9TermParserA
import scala.util.parsing.combinator.Parsers
import scala.collection.immutable.{HashMap, Stack}

object LKProofParser {
  def debug(s:String) = { println(s) }

  type ProofMap = HashMap[String,LKProof]
  val emptyProofMap = HashMap.empty[String,LKProof]
  type LabeledProof = (String,LKProof)


  def parseProofs(input: InputStreamReader): List[(String, LKProof)] = {
    val m = LKProofParser.parseProof(input)
    m.proofs
  }

  def parseProofFlat(txt: InputStreamReader): Map[String, LKProof] =
  {
    val proofdb = parseProof( txt )
    Map.empty[String, LKProof] ++ (proofdb.proofs)
  }

  //plabel should return the proof corresponding to this label
  def parseProof(txt: InputStreamReader): ProofDatabase = {
    lazy val sp = new SimpleLKParser with Prover9TermParserA {
      def getInput = txt
      override def conssymb: Parser[String] = """([a-tA-Z][a-zA-Z0-9_]*)|([0-9]+)""".r
      override def varsymb: Parser[String] =  """[u-z][a-zA-Z0-9_]*""".r
    }

    sp.parseAll[List[LabeledProof]](sp.hlk_file, txt) match {
      case sp.Success(result, input) =>
        println("YAY!!")
        println(result)
        //sp.getProofDB
        val db = new ProofDatabase(Map.empty, result, Nil, Nil)
        db

      case sp.NoSuccess(msg, input) =>
        throw new Exception("Parser failed at "+input.pos+ " with message: "+msg)
    }
  }
}

abstract trait HLKFormulaParser extends Parsers {
  //abstract parsers for formulas
  def term: Parser[HOLExpression];
  def formula: Parser[HOLFormula];
  def variable: Parser[HOLVar];

}



package incomplete {
  /* incomplete.Inference captures the notion of an inference where the parents are only known by name  */

  import LKProofParser.ProofMap
  import LKProofParser.LabeledProof

  sealed case class Inference(name : String,
                              create : (ProofMap, List[LabeledProof]) => (LKProof, List[LabeledProof]) ) { }
}

abstract trait SimpleLKParser extends JavaTokenParsers with HLKFormulaParser {
  import LKProofParser.debug
  import LKProofParser.LabeledProof
  import LKProofParser.ProofMap
  import LKProofParser.emptyProofMap

  //override val whiteSpace = """\s+""".r


  //maps to prevent passing around lots of parameters


  /* automatic generation of labels */
  private var labels : Set[String] = Set.empty
  private var labelcount = 100
  private def getLabel = {
    while (labels.contains("l"+labelcount))
      labelcount = labelcount +1
    val newlabel = "l"+labelcount
    labels = labels + newlabel
    newlabel
  }


  /*
  def getProofDB : ProofDatabase = {
    debug("subproofs:")
    subproofs map (x => debug(x._1 + " : " + x._2.root))
    new ProofDatabase(Map.empty[HOLExpression,HOLExpression], proofs.toList, Nil, Nil)
  }
    */

  // hardcoded syntax conventions
  val proof_name : Parser[String] = """[\\]*[a-z]*[0-9]*""".r
  val name = """(\\)?[a-z0-9_]+""".r
  val label = """[a-zA-Z0-9]+""".r

  /* some definitions which allow easier change of the language */
  val sleft = "left"
  val sright ="right"
  val saxiom = "axiom"
  val sall = "all"
  val sex = "exists"
  val sand ="and"
  val sor = "or"
  val simpl = "impl"
  val scontr = "contr"
  val sweak = "weak"
  val scut = "cut"
  val sautoprop = "autoprop"




  def hlk_file: Parser[List[LabeledProof]] =  rep1(lkProof) ^^ complete_proofs

  def line: Parser[List[incomplete.Inference]] =  proof.+


  def complete_proofs(iproofs : List[(String,FSequent, List[incomplete.Inference])]) : List[LabeledProof] = complete_proofs_(iproofs, emptyProofMap)
  def complete_proofs_(iproofs : List[(String,FSequent, List[incomplete.Inference])], global : ProofMap) : List[LabeledProof] =
    iproofs match {
      case Nil =>
        throw new Exception("Empty proof lists not supported!")
      case (name, endsequent, isubproofs) :: Nil =>
        val proof = complete_proof(endsequent, isubproofs, global)
        List((name,proof))

      case (name, endsequent, isubproofs) :: rest =>
        val proof = complete_proof(endsequent, isubproofs, global)
        val nglobal = global + ((name,proof))
        (name, proof) :: complete_proofs_(rest, nglobal)
    }


  def complete_proof(endsequent:FSequent, subproofs : List[incomplete.Inference], global : ProofMap) : LKProof = {
    println(subproofs.map(_.name).mkString(", "))
    complete_proof_(endsequent, subproofs, global)._1
  }
  def complete_proof_(endsequent:FSequent, subproofs : List[incomplete.Inference], global : ProofMap ) : (LKProof, List[(String,LKProof)]) = subproofs match {
    case Nil => throw new Exception("Cannot create proof, no inferences to complete!")
    case List(inf) =>
      inf.create(global, Nil)
    case inf :: rest =>
      val (p, local)  = complete_proof_(endsequent, rest, global)
      inf.create(global, local)
  }


  def lkProof: Parser[(String, FSequent, List[incomplete.Inference])] = ("proof" ~> name) ~ ("proves" ~> sequent)  ~ ("{" ~> line <~ "}")   ^^ {
    case  proofname ~  endsequent ~ line => {
      /*
      println(line)
      proofs.put(proofname, stackOfProofs.head)
      subproofs.put(proofname, stackOfProofs.head)
      stackOfProofs.head
      */
      (proofname, endsequent, line)
    }
  }


  def proof: Parser[incomplete.Inference] = (ax | neg| cut | binaryOrAnd | unaryAndOr |
     weak | contr | strong_quantifier | weak_quantifier | impL | impR |
     autoprop) ~ opt("[" ~> label <~ "]") <~ ";" ^^ { _ match {
        case p ~ None =>
          debug("generating label")
          /*
          stackOfProofs = stackOfProofs.push(p);
          subproofs.put(label, p)
          */
          val label = getLabel
          incomplete.Inference(p.name, (global,local) => {
            val (proof, list) = p.create(global, local)
            (proof, (label,proof) :: list )
          })

        case p ~ Some(label) =>
          debug("using label "+label)
          /*
          stackOfProofs = stackOfProofs.push(p);
          subproofs.put(label, p)
          */
          incomplete.Inference(p.name, (global,local) => {
            val (proof, list) = p.create(global, local)
            (proof, (label,proof) :: list )
          })
      }
     }




  //      def sequent: Parser[Sequent] = formula ~ "|-" ~ formula ^^ { case lf ~ "|-" ~ rf => {
  def sequent: Parser[FSequent] = repsep(formula,",") ~ ":-" ~ repsep(formula,",") ^^ {
    case lfs ~ ":-" ~ rfs => {
      //          println("SEQUENT")
      FSequent(lfs, rfs)
    }
  }

  /* ========== axiom rules ========================== */

  def ax: Parser[incomplete.Inference] = saxiom ~> "(" ~> sequent <~ ")" ^^ { sequent =>
    debug("axiom!")
    incomplete.Inference("axiom", (global, local) => {
      val inf = Axiom(sequent.antecedent, sequent.succedent)
      (inf, local)
    } )
  }

  /*
  def pFOLink: Parser[incomplete.Inference] = "pLink(" ~ "(" ~ proof_name ~ "," ~ index ~ ")"  ~ sequent ~ ")" ^^ {
    case                       "pLink(" ~ "(" ~ name ~       "," ~   v   ~ ")"  ~ sequent ~ ")" => {
      debug("pLink")
      FOSchemaProofLinkRule(sequent, name, v::Nil)
    }
  }
  */

  /* ========== structural rules ===================== */
  def cut: Parser[incomplete.Inference] = scut ~> "(" ~> formula <~ ")" ^^ {
    case f => {
      incomplete.Inference("cut", (global, local) => {
        require(local.length >= 2, "Problem in proof structure!")
        val (_,top1)::(_,top2)::rest = local
        val inf : LKProof = CutRule(top1, top2, f)
        (inf, rest)
      } )

    }
  }


  def contr: Parser[incomplete.Inference] = scontr ~> (sleft | sright) ~ ("(" ~> formula) <~ ")" ^^ {
    case "left" ~f  => incomplete.Inference ("c:l", (global, local) => {
      debug("contrL")
      require(local.length >= 1, "Problem in proof structure!")
      val (_,top)::rest = local
      val inf : LKProof = ContractionLeftRule(top, f)
      (inf, rest)
    })

    case "right" ~ f  => incomplete.Inference ("c:r", (global, local) => {
      debug("contrR")
      require(local.length >= 1, "Problem in proof structure!")
      val (_,top)::rest = local
      val inf : LKProof = ContractionRightRule(top, f)
      (inf, rest)
    })

  }


  def weak: Parser[incomplete.Inference] = sweak ~> (sright|sleft) ~ ("(" ~> formula <~ ")") ^^ {
    case "left" ~ formula =>
      debug("weak right "+formula)
      incomplete.Inference("w:l", (global, local) =>  {
        require(local.length >= 1, "Problem in proof structure!")
        val (_,top) :: rest = local
        (WeakeningLeftRule(top, formula), rest)
      })

    case "right" ~ formula  =>
      debug("weak right "+formula)
      incomplete.Inference("w:r", (global, local) =>  {
        require(local.length >= 1, "Problem in proof structure!")
        val (_,top) :: rest = local
        (WeakeningRightRule(top, formula), rest)
      })
  }

  /* ================ logical rules ======================= */

  def neg: Parser[incomplete.Inference] = "neg" ~> (sleft|sright) ~  ("(" ~> formula) <~ ")" ^^ {
    case "left" ~ formula=>
      incomplete.Inference("n:l",  (global, local) => {
        require(local.length >= 1, "Problem in proof structure!")
        val (_,top)::rest = local
        val inf = NegLeftRule(top, formula)
        (inf, rest)
      })
    case "right" ~ formula =>
      incomplete.Inference("n:r", (global, local) => {
        require(local.length >= 1, "Problem in proof structure!")
        val (_,top)::rest = local
        val inf = NegLeftRule(top, formula)
        (inf, rest)
      })
  }

  def unaryAndOr: Parser[incomplete.Inference] = ((sand ~ sleft ~ "([12])?".r) |  (sor ~ sright ~ "([12])?".r)  ) ~ ("by" ~> label).? ~ (":" ~> formula) ~ ("," ~> formula)  ^^ { r =>
    /*
    val (parent, rest) = r match {
      case _ ~ _ ~ Some(label) ~ _ ~ _ =>
        if ()
        require(parent != null , "Referring to unknown label "+label)
      case _ ~ _ ~ None ~ _ ~ _ =>
        require(parent != null , "Referring to unknown label "+label)
    } */
    val name : String = r match { case r ~ s ~ t ~ _ ~ _ ~ _ => List(r,s,t).mkString(" ")}

    incomplete.Inference(name, (global, local) => {
      require(local.length >= 1, "Problem in proof structure!")
      val (_,parent) :: rest = local

      val inf = r match {
        case "or" ~ "right" ~ "" ~ l ~ f1  ~ f2 =>
          OrRightRule(parent, f1, f2)
        case "or" ~ "right" ~ "1" ~ l ~ f1  ~ f2 =>
          OrRight1Rule(parent, f1, f2)
        case "or" ~ "right" ~ "2" ~ l ~ f1  ~ f2 =>
          OrRight2Rule(parent, f1, f2)
        case "and" ~ "left" ~ "" ~ l ~ f1  ~ f2 =>
          AndLeftRule(parent, f1, f2)
        case "and" ~ "left" ~ "1" ~ l ~ f1  ~ f2 =>
          AndLeft1Rule(parent, f1, f2)
        case "and" ~ "left" ~ "2" ~ l ~ f1  ~ f2 =>
          AndLeft2Rule(parent, f1, f2)
      }

      (inf,rest)

    })
  }

  def binaryOrAnd: Parser[incomplete.Inference] = ((sor ~ sleft) | (sand ~ sright)) ~ ("(" ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case "or" ~ "left" ~ f1 ~ f2  => incomplete.Inference("or:l", (global, local) => {
      debug("orL")
      require(local.length >= 2, "Problem in proof structure!")
      val (_,parent1)::(_,parent2)::rest = local
      val inf : LKProof = OrLeftRule(parent1, parent2, f1, f2)
      (inf,rest)
    })
    case "and" ~ "right" ~ f1 ~ f2 => incomplete.Inference("and:r",(global, local) => {
      debug("andR")
      require(local.length >= 2, "Problem in proof structure!")
      val (_,parent1)::(_,parent2)::rest = local
      val inf : LKProof = AndRightRule(parent1, parent2, f1, f2)
      (inf,rest)
    })
  }


  def impL: Parser[incomplete.Inference] = (simpl ~> sleft ~> "(" ~> formula) ~ ("," ~> formula) <~ ")" ^^ {
    case f1 ~ f2  => incomplete.Inference("imp:l", (global, local) => {
      require(local.length >= 2, "Problem in proof structure!")
      val (_, parent1)::(_, parent2) :: rest = local
      val inf = ImpLeftRule(parent1, parent2, f1, f2)
      (inf,rest)
    })
  }

  def impR: Parser[incomplete.Inference] = (simpl ~> sright ~> "(" ~> formula) ~ ("," ~> formula <~ ")") ^^ {
    case f1 ~ f2 => incomplete.Inference("imp:r", (global, local) => {
      require(local.length >= 1, "Problem in proof structure!")
      val (_, parent) :: rest = local
      val inf = ImpRightRule(parent, f1, f2)
      (inf, rest)
    })
  }


  def weak_quantifier: Parser[incomplete.Inference] = ((sall ~ sleft) | (sex ~ sright)) ~ ("(" ~> formula) ~ ("," ~> formula) ~ ("," ~> term) <~ ")" ^^ {
    case "all" ~ "left" ~aux ~ main ~ term =>  incomplete.Inference("all:l", (global, local) => {
      require(local.length >= 1, "Problem in proof structure!")
      val (_, parent) :: rest = local
      val inf = ForallLeftRule(parent, aux, main, term)
      (inf, rest)
    })

    case "exists" ~ "right" ~ aux ~ main ~ term =>  incomplete.Inference("ex:r", (global, local) => {
      require(local.length >= 1, "Problem in proof structure!")
        val (_, parent) :: rest = local
        val inf = ExistsRightRule(parent, aux, main, term)
        (inf,rest)
    })

  }

  def strong_quantifier: Parser[incomplete.Inference] = ((sall ~ sright) | (sex ~ sleft)) ~  ("(" ~> formula) ~ ("," ~> formula) ~ ("," ~> (variable)) <~ ")" ^^ {
    case "all" ~ "right" ~ aux ~ main ~ v  =>  incomplete.Inference("all:r", (global, local) => {
      require(local.length >= 1, "Problem in proof structure!")
      val (_, parent) :: rest = local
      val inf = ForallRightRule(parent, aux, main, v)
      (inf, rest)
    })
    case "exists" ~ "left" ~ aux ~ main ~ v  =>  incomplete.Inference("ex:l", (global, local) => {
      require(local.length >= 1, "Problem in proof structure!")
        val (_, parent) :: rest = local
        val inf = ExistsLeftRule(parent, aux, main, v)
      (inf,rest)
    })
  }


  def autoprop: Parser[incomplete.Inference] = sautoprop ~> "(" ~> sequent <~ ")" ^^ { seq  =>
    incomplete.Inference("autoprop", (global, local) => (solvePropositional.autoProp(seq), local)  )
  }


  def applyContr (f: HOLFormula, p:LKProof): LKProof = {
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


// trying to separate formula parsing from language parsing
trait SchemaFormulaParser extends HLKFormulaParser with HOLParser {
    import LKProofParser.debug

    def goal = term

    var predicate_arities = Map.empty[String, Int]

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
        {
          predicate_arities = predicate_arities + ((x.toString, l.size))
          predicate_arities
        }
        else if (predicate_arities.get(x.toString).get != l.size ) {
          println("Input ERROR : Indexed Predicate '"+x.toString+"' should have arity "+predicate_arities.get(x.toString).get+ ", but not "+l.size+" !")
          throw new Exception("Input ERROR : Indexed Predicate '"+x.toString+"' should have arity "+predicate_arities.get(x.toString).get+ ", but not "+l.size+" !")
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
        debug("prefix")
        Tuple4(true, intVar1, ind1, ind2)
      }
      case "BigOr" ~ "(" ~ intVar1 ~ "=" ~ ind1 ~ ".." ~ ind2 ~ ")"  => {
        debug("prefix")
        Tuple4(false, intVar1, ind1, ind2)
      }
    }

  }

