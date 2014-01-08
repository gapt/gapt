package at.logic.parsing.veriT

import scala.util.parsing.combinator._
import at.logic.language.fol._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.BetaReduction._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.calculi.expansionTrees.{ExpansionTree, WeakQuantifier, prenexToExpansionTree, qFreeToExpansionTree}
import java.io.FileReader
import at.logic.utils.logging.Logger

object VeriTParserLogger extends Logger

object VeriTParser extends RegexParsers {

  type Instances = (FOLFormula, List[FOLFormula])

  def genEqualities(pairs: List[(FOLTerm, FOLTerm)], eqs: List[FOLFormula]) = {
    
    // Transforms the equalities provided into a list of pairs
    val eqs_pairs = eqs.map(f => f match {
      case Neg(Atom(_, List(a, b))) => (a, b)
    })

    // Checking which equalities were in the wrong order and generating the symmetry instances
    val symm = pairs.foldLeft(List[Instances]()) ( (acc, p) =>
      if ( eqs_pairs.contains((p._2, p._1)) ) {
        acc :+ getSymmInstances(p._2, p._1)
      }
      else {
        assert(eqs_pairs.contains(p))
        acc
      }
    )

    // Generate the correct equalities
    val eqs_correct = pairs.foldRight(List[FOLFormula]()) {
      case (p, acc) => 
        val eq = ConstantStringSymbol("=")
        Atom(eq, List(p._1, p._2)) :: acc
    }
    
    (eqs_correct, symm)
  }

  def getSymmInstances(a: FOLTerm, b: FOLTerm) : Instances = {
    val x = FOLVar(VariableStringSymbol("x"))
    val y = FOLVar(VariableStringSymbol("y"))
    val eq = ConstantStringSymbol("=")
    val eq1 = Atom(eq, List(x, y))
    val eq2 = Atom(eq, List(y, x))
    val imp = Imp(eq1, eq2)
    val eq_symm = AllVar(x, AllVar(y, imp))

    val i1 = eq_symm.instantiate(a).instantiate(b)
    val i2 = eq_symm.instantiate(b).instantiate(a)

    (eq_symm, List(i1, i2))
  }
  
  def getEqReflInstances(f: List[FOLFormula]) : List[Instances] = {
    val x = FOLVar(VariableStringSymbol("x"))
    val eq = ConstantStringSymbol("=")
    val eq_refl = AllVar(x, Atom(eq, List(x, x)))
    List((eq_refl, f))
  }

  // Assuming all the antecedents of the implication are ordered:
  // ( =(x0, x1)  ^  =(x1, x2)  ^ ... ^  =(xn-1, xn)  ->  =(x0, xn) )
  // in veriT is *always* ( not =(x0, x1) , not =(x1, x2) , ... , not =(xn-1, xn) , =(x0, xn) )
  def getEqTransInstances(l: List[FOLFormula]) : List[Instances] = {
    val x = FOLVar(VariableStringSymbol("x"))
    val y = FOLVar(VariableStringSymbol("y"))
    val z = FOLVar(VariableStringSymbol("z"))
    val eq = ConstantStringSymbol("=")
    val eq1 = Atom(eq, List(x, y))
    val eq2 = Atom(eq, List(y, z))
    val eq3 = Atom(eq, List(x, z))
    val imp = Imp(And(eq1, eq2), eq3)
    val eq_trans = AllVar(x, AllVar(y, AllVar(z, imp)))

    var symm = List[Instances]()

    // Transforms a transitivity chain (represented as a list):
    //
    // [ not =(x0, x1) , not =(x1, x2) , ... , not =(xn-1, xn) , =(x0, xn) ]
    //
    // into simple transitivity formulas:
    //
    // =(x0, x1) ^ =(x1, x2) -> =(x0, x2)
    // =(x0, x2) ^ =(x2, x3) -> =(x0, x3)
    // ...
    // =(x0, xn-1) ^ =(xn-1, xn) -> =(x0, xn)
    //
    def unfoldChain(l: List[FOLFormula]) = unfoldChain_(l.tail, l(0))
    def unfoldChain_(l: List[FOLFormula], c: FOLFormula) : List[FOLFormula] = l.head match {
      case Neg(Atom(eq0, List(x0, x1))) if eq0 == eq => c match {
        // Note that the variables are:
        // x2=x3 ^ x0=x1
        // Checking all possible cases of atom ordering:
 
        // x=y ^ y=z -> x=z
        case Neg(Atom(eq1, List(x2, x3))) if x3 == x0 =>
          val newc = Neg(Atom(eq, List(x2, x1)))
          // Instances
          val f1 = eq_trans.instantiate(x2)
          val f2 = f1.instantiate(x0) // or x3, should be the same
          val f3 = f2.instantiate(x1)

          f3 :: unfoldChain_(l.tail, newc)

        // x=y ^ z=y -> x=z
        case Neg(Atom(eq1, List(x2, x3))) if x3 == x1 =>
          val newc = Neg(Atom(eq, List(x2, x0)))
          // Instances
          val f1 = eq_trans.instantiate(x2)
          val f2 = f1.instantiate(x1) // or x3, should be the same
          val f3 = f2.instantiate(x0)

          symm = getSymmInstances(x0, x1) :: symm

          f3 :: unfoldChain_(l.tail, newc)

        // y=x ^ z=y -> x=z
        case Neg(Atom(eq1, List(x2, x3))) if x2 == x1 =>
          val newc = Neg(Atom(eq, List(x3, x0)))
          // Instances
          val f1 = eq_trans.instantiate(x3)
          val f2 = f1.instantiate(x1) // or x2, should be the same
          val f3 = f2.instantiate(x0)

          symm = getSymmInstances(x0, x1) :: symm
          symm = getSymmInstances(x2, x3) :: symm
          
          f3 :: unfoldChain_(l.tail, newc)
        
        // y=x ^ y=z -> x=z
        case Neg(Atom(eq1, List(x2, x3))) if x2 == x0 =>
          val newc = Neg(Atom(eq, List(x3, x1)))
          // Instances
          val f1 = eq_trans.instantiate(x3)
          val f2 = f1.instantiate(x0) // or x2, should be the same
          val f3 = f2.instantiate(x1)
          
          symm = getSymmInstances(x2, x3) :: symm

          f3 :: unfoldChain_(l.tail, newc)

        case Neg(Atom(eq1, List(x2, x3))) => 
          val msg = "ERROR: the conclusion of the previous terms have" +  
          " no literal in common with the next one. Are the literals out of order?" + 
          "\nconclusion: " + c + "\nsecond literal: " + l.head
          VeriTParserLogger.error(msg)
          throw new Exception(msg)

        case _ => 
          val msg = "ERROR: wrong format for negated equality: " + c
          VeriTParserLogger.error(msg)
          throw new Exception(msg)
      }

      case Neg(Atom(eq0, List(x0, x1))) if eq0 != eq => 
        val msg = "ERROR: Predicate " + eq0 + " in eq_transitive is not equality."
        VeriTParserLogger.error(msg)
        throw new Exception(msg)
      
      // When reaching the final literal, check if they are the same.
      case Atom(eq0, List(x0, x1)) if eq0 == eq => c match {
        case Neg(Atom(eq1, List(x2, x3))) if x0 == x2 && x1 == x3 => Nil
        case Neg(Atom(eq1, List(x2, x3))) if x1 == x2 && x0 == x3 => Nil
        
        case Neg(Atom(eq1, List(x2, x3))) => 
          val msg = "ERROR: the conclusion of the previous terms" + 
          " have no literal in common with the conclusion of the chain. Are the literals out of order? Is the conclusion" + 
          " not the last one?"
          VeriTParserLogger.error(msg)
          throw new Exception(msg)

        case _ => 
          val msg = "ERROR: wrong format for negated equality: " + c
          VeriTParserLogger.error(msg)
          throw new Exception(msg)
      }

      case Atom(eq0, List(x0, x1)) if eq0 != eq => 
        val msg = "ERROR: Predicate " + eq0 + " in eq_transitive is not equality."
        VeriTParserLogger.error(msg)
        throw new Exception(msg)
    }

    val instances = unfoldChain(l)
    (eq_trans, instances) :: symm
  }

  // Assuming all the antecedents of the implication are ordered:
  // ( =(x0, y0)  ^  =(x1, y1)  ^ ... ^  =(xn, yn)  ->  =(f x0...xn, f y0...yn) )
  // in veriT is *always* ( not =(x0, y0) , not =(x1, y1) , ... , not =(xn, yn), =(f x0...xn, f y0...yn) )
  def getEqCongrInstances(f: List[FOLFormula]) : List[Instances] = {

    def getFunctionName(f: FOLFormula) : String = f match {
      case Atom(eq, List(f1, _)) => f1 match {
        case Function(ConstantStringSymbol(n), _) => n 
      }
    }
    
    def getArgsLst(f: FOLFormula) = f match {
      case Atom(eq, List(f1, f2)) => (f1, f2) match {
        case (Function(_, args1), Function(_, args2)) => (args1, args2) 
      }
    }

    // Generate the eq_congruent formula with the right number of literals
    def gen_eq_congr(n: Int, fname: String) : FOLFormula = {
      val listX = (for{i <- 1 to n} yield FOLVar(VariableStringSymbol("x" + i)) ).toList
      val listY = (for{i <- 1 to n} yield FOLVar(VariableStringSymbol("y" + i)) ).toList
      val equalities = listX.zip(listY).foldRight(List[FOLFormula]()) {
        case (p, acc) => 
          val eq = ConstantStringSymbol("=")
          Atom(eq, List(p._1, p._2)) :: acc
      }
      val conj = And(equalities)
      val name = ConstantStringSymbol(fname)
      val f1 = Function(name, listX)
      val f2 = Function(name, listY)
      val eq = ConstantStringSymbol("=")
      val last_eq = Atom(eq, List(f1, f2))
      val matrix = Imp(conj, last_eq)

      val quantY = listY.foldRight(matrix) {
        case (yi, f) => AllVar(yi, f)
      }

      listX.foldRight(quantY) {
        case (xi, f) => AllVar(xi, f)
      }
    }

    val fname = getFunctionName(f.last)
    val n = getArgsLst(f.last)._1.size
    val eq_congr = gen_eq_congr(n, fname)
    
    val (args1, args2) = getArgsLst(f.last)
    val pairs = args1.zip(args2)
    val (eqs_correct, symm) = genEqualities(pairs, f.dropRight(1))
    val instance = Imp(And(eqs_correct), f.last)

    ((eq_congr, List(instance)) :: symm)
  }

  // Assuming all the antecedents of the implication are ordered:
  // ( =(x0, y0)  ^  =(x1, y1)  ^ ... ^  =(xn, yn) ^ p(x0...xn)  ->  p(y0...yn) )
  // in veriT is *always* 
  // ( not =(x0, y0) , not =(x1, y1) , ... , not =(xn, yn), not p(x0...xn), p(y0...yn) )
  // or
  // ( not =(x0, y0) , not =(x1, y1) , ... , not =(xn, yn), p(x0...xn), not p(y0...yn) )
  def getEqCongrPredInstances(f: List[FOLFormula]) : List[Instances] = {

    def getPredName(f: FOLFormula) : String = f match {
      case Atom(p, _) => p match {
          case ConstantStringSymbol(n) => n 
      }
      case Neg(Atom(p, _)) => p match {
          case ConstantStringSymbol(n) => n 
      }
    }

    def getArgsLst(p1: FOLFormula, p2: FOLFormula) = (p1, p2) match {
      case ( Neg(Atom(_, args1)), Atom(_, args2) ) => (args1, args2)
      case ( Atom(_, args1), Neg(Atom(_, args2)) ) => (args2, args1)
    }

    // Generate the eq_congruent_pred with the right number of literals
    def gen_eq_congr_pred(n: Int, pname: String) : FOLFormula = {
      val listX = (for{i <- 1 to n} yield FOLVar(VariableStringSymbol("x" + i)) ).toList
      val listY = (for{i <- 1 to n} yield FOLVar(VariableStringSymbol("y" + i)) ).toList
      val equalities = listX.zip(listY).foldRight(List[FOLFormula]()) {
        case (p, acc) => 
          val eq = ConstantStringSymbol("=")
          Atom(eq, List(p._1, p._2)) :: acc
      }
      val name = ConstantStringSymbol(pname)
      val p1 = Atom(name, listX)
      val p2 = Atom(name, listY)
      val conj = And(equalities :+ p1)
      val matrix = Imp(conj, p2)

      val quantY = listY.foldRight(matrix) {
        case (yi, f) => AllVar(yi, f)
      }

      listX.foldRight(quantY) {
        case (xi, f) => AllVar(xi, f)
      }
    }

    val pname = getPredName(f.last)
    val n = getArgsLst(f(f.length-2), f(f.length-1))._1.size
    val eq_congr_pred = gen_eq_congr_pred(n, pname)
    
    val (args1, args2) = getArgsLst(f(f.length-2), f(f.length-1))
    val pairs = args1.zip(args2)
    val (eqs_correct, symm) = genEqualities(pairs, f.dropRight(2))
    val (p1, p2) = (f(f.length-2), f(f.length-1)) match { 
      case (Neg(f1), f2) => (f1, f2)
      case (f1, Neg(f2)) => (f2, f1)
    }
    val instance = Imp(And(eqs_correct :+ p1), p2)
    
    ((eq_congr_pred, List(instance)) :: symm)
  }

  def getExpansionProof(filename : String) : Option[(Seq[ExpansionTree], Seq[ExpansionTree])] = {
    VeriTParserLogger.trace("FILE: " + filename)
    try {
      parseAll(proof, new FileReader(filename)) match {
        case Success(r, _) => r
        case Failure(msg, next) => 
          val msg0 = "VeriT parsing: syntax failure " + msg + "\nat line " + next.pos.line + " and column " + next.pos.column
          VeriTParserLogger.error(msg0)
          throw new Exception(msg0)
        case Error(msg, next) => 
          val msg0 = "VeriT parsing: syntax error " + msg + "\nat line " + next.pos.line + " and column " + next.pos.column
          VeriTParserLogger.error(msg0)
          throw new Exception(msg0)
      }
    } catch {
      case e : OutOfMemoryError => 
        val msg = "Out of memory during parsing."
        VeriTParserLogger.error(msg + ": " + e)
        throw e
      case e : Throwable =>
        val msg = "Unknown error during parsing."
        VeriTParserLogger.error(msg + ": " + e)
        throw e
    }
  }

  def isUnsat(filename: String) : Boolean = {
    parseAll(parseUnsat, new FileReader(filename)) match {
      case Success(r, _) => r
      case Failure(msg, next) => 
        val msg0 = "VeriT parsing: syntax failure " + msg + "\nat line " + next.pos.line + " and column " + next.pos.column
        throw new Exception(msg0)
      case Error(msg, next) => 
        val msg0 = "VeriT parsing: syntax error " + msg + "\nat line " + next.pos.line + " and column " + next.pos.column
        throw new Exception(msg0)
    }   
  }

  // Each list of formulas corresponds to the formulas occurring in one of the axioms.
  def proof : Parser[Option[(Seq[ExpansionTree], Seq[ExpansionTree])]] = rep(header) ~> rep(preprocess) ~ rep(rules) ^^ {

    // Relying on the fact that if the formula is unsatisfiable, a proof is
    // always printed. If there is no proof, the result is sat.
    case Nil ~ Nil => None
    
    case pp ~ r => 
     
      val input = pp.last
      val axioms = r.flatten
      
      // Join the instances of the same quantified formula
      val keys = axioms.map(p => p._1).distinct 
      val joinedInst = keys.foldLeft(List[Instances]()) {case (acc, f) =>
        val keyf = axioms.filter(p => p._1 == f)
        val allInst = keyf.foldLeft(List[FOLFormula]()) ((acc, p) => p._2 ++ acc)
        (f, allInst.distinct) :: acc
      }
      // Transform all pairs into expansion trees
      val inputET = input.map(p => qFreeToExpansionTree(p))
      val axiomET = joinedInst.map(p => prenexToExpansionTree(p._1, p._2))
      val ant = axiomET ++ inputET

      val cons = List()
      Some( (ant.toSeq, cons.toSeq) )
  }

  def parseUnsat : Parser[Boolean] = title ~ rep(success) ~> (unsat ^^ { case s => true } | sat ^^ { case s => false }) <~ success
  
  def label : Parser[String] = ".c" ~ """\d+""".r ^^ { case s1 ~ s2 => s1 ++ s2 }
  
  // FILE HEADER
  def header : Parser[String] = success | unsat | sat | title | msg
  def success : Parser[String] = "success"
  def unsat : Parser[String] = "unsat"
  def sat : Parser[String] = "sat"
  // TODO: find out what is the general format of this title.
  def title : Parser[String] = "verit dev - the VERI(T) theorem prover (UFRN/LORIA)." | "veriT 201310d - the SMT-solver veriT (UFRN/LORIA)."
  def msg : Parser[String] = "Formula is Satisfiable"
 
  // INPUT PROCESSING RULES
  // Get only the formula on the last one of these rules.
  def preprocess : Parser[List[FOLFormula]] = "(set" ~ label ~ "(" ~> rulePreProc <~ "))"
  def rulePreProc : Parser[List[FOLFormula]] = input | tmp_distinct_elim | tmp_alphaconv | tmp_let_elim 
  def input : Parser[List[FOLFormula]] = "input" ~> conclusion
  def tmp_distinct_elim : Parser[List[FOLFormula]] = "tmp_distinct_elim" ~ premises ~> conclusion  
  def tmp_alphaconv : Parser[List[FOLFormula]] = "tmp_alphaconv" ~ premises ~> conclusion
  def tmp_let_elim : Parser[List[FOLFormula]] = "tmp_let_elim" ~ premises ~> conclusion

  // RESOLUTION RULES AND EQUALITY AXIOMS
  def rules : Parser[List[Instances]] = "(set" ~ label ~ "(" ~> rule <~ "))"
  def rule : Parser[List[Instances]] = eqAxiom | innerRule
  def eqAxiom : Parser[List[Instances]] = eq_reflexive | eq_transitive | eq_congruence | eq_congruence_pred
  def eq_reflexive : Parser[List[Instances]] = "eq_reflexive" ~> conclusion ^^ {
    case c => 
      getEqReflInstances(c)
  }
  def eq_transitive : Parser[List[Instances]] = "eq_transitive" ~> conclusion ^^ {
    case c => 
      getEqTransInstances(c)
  }
  def eq_congruence : Parser[List[Instances]] = "eq_congruent" ~> conclusion ^^ {
    case c => 
      getEqCongrInstances(c)
  }
  def eq_congruence_pred : Parser[List[Instances]] = "eq_congruent_pred" ~> conclusion ^^ {
    case c => 
      getEqCongrPredInstances(c)
  }

  def innerRule : Parser[List[Instances]] = resolution | and | and_pos | or | or_pos | and_neg | not_and | not_or | or_neg | implies | implies_pos | implies_neg1 | implies_neg2 | not_implies1 | not_implies2
  // Rules that I don't care
  // TODO: parse all rules
  def resolution : Parser[List[Instances]] = "resolution" ~> premises <~ conclusion
  def and : Parser[List[Instances]] = "and" ~> premises <~ conclusion
  def and_pos : Parser[List[Instances]] = "and_pos" ~> conclusion  ^^ { case _ => Nil }
  def and_neg : Parser[List[Instances]] = "and_neg" ~> conclusion ^^ { case _ => Nil }
  def or : Parser[List[Instances]] = "or" ~> premises <~ conclusion
  def or_pos : Parser[List[Instances]] = "or_pos" ~> conclusion ^^ { case _ => Nil }
  def or_neg : Parser[List[Instances]] = "or_neg" ~> conclusion ^^ { case _ => Nil }
  def implies : Parser[List[Instances]] = "implies" ~> premises <~ conclusion 
  def implies_pos : Parser[List[Instances]] = "implies_pos" ~> conclusion ^^ { case _ => Nil }
  def implies_neg1 : Parser[List[Instances]] = "implies_neg1" ~> conclusion ^^ { case _ => Nil }
  def implies_neg2 : Parser[List[Instances]] = "implies_neg2" ~> conclusion ^^ { case _ => Nil }
  def not_implies1 : Parser[List[Instances]] = "not_implies1" ~> premises <~ conclusion
  def not_implies2 : Parser[List[Instances]] = "not_implies2" ~> premises <~ conclusion
  def not_and : Parser[List[Instances]] = "not_and" ~> premises <~ conclusion
  def not_or : Parser[List[Instances]] = "not_or" ~> premises <~ conclusion
  
  // I don't care about premises. I only use the leaves
  def premises : Parser[List[Instances]] = ":clauses (" ~ rep(label) ~ ")" ^^ { case _ => Nil}
  def conclusion : Parser[List[FOLFormula]] = ":conclusion (" ~> rep(expression) <~ ")"
 
  def expression : Parser[FOLFormula] = formula | let
  def formula : Parser[FOLFormula] = andFormula | orFormula | notFormula | pred
  
  def term : Parser[FOLTerm] = constant | function 
  def constant : Parser[FOLTerm] = name ^^ { case n => FOLConst(ConstantStringSymbol(n)) }
  def function : Parser[FOLTerm] = "(" ~> name ~ rep(term) <~ ")" ^^ {
    case name ~ args => 
      val n = ConstantStringSymbol(name) 
      Function(n, args)
  }

  def andFormula : Parser[FOLFormula] = "(and" ~> rep(formula) <~ ")" ^^ { 
    case flst => And(flst)
  }
  def orFormula : Parser[FOLFormula] = "(or" ~> rep(formula) <~ ")" ^^ { 
    case flst => Or(flst)
  }
  def implFormula : Parser[FOLFormula] = "(=>" ~> rep(formula) <~ ")" ^^ { 
    case flst => 
      val last = flst(flst.size-1)
      val second_last = flst(flst.size-2)
      val rest = flst.dropRight(2)
      val imp = Imp(second_last, last)
      rest.foldRight(imp) { case (f, acc) => Imp(f, acc) }
  }
  def notFormula : Parser[FOLFormula] = "(not" ~> formula <~ ")" ^^ { 
    case f => Neg(f)
  }
  def pred : Parser[FOLFormula] = "(" ~> name ~ rep(term) <~ ")" ^^ { 
    case name ~ args => 
      val n = ConstantStringSymbol(name)
      Atom(n, args)
  } | name ^^ {
    // No parenthesis around unary symbols
    case name => Atom(ConstantStringSymbol(name), Nil)
  }

  // Syntax of let-expressions:
  // (let (v1 t1) ... (vn tn) exp)
  // which is equivalent to the lambda-expression:
  // (\lambda v1 ... vn exp) t1 ... tn
  // But we are not constructing the terms for now, first because we don't need 
  // it and second because the garbage collector goes crazy and crashes while
  // constructing this huge lambda-term
  def let : Parser[FOLFormula] = "(" ~> "let" ~> "(" ~> rep(binding) ~ ")" ~ expression <~ ")" ^^ {
    case _ => Or(List())
  }

  def binding : Parser[(FOLTerm, FOLTerm)] = "(" ~> constant ~ term <~ ")" ^^ {
    case v ~ t => (v, t)
  }
  
  def name : Parser[String] = """[^ ():]+""".r

}
