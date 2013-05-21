package at.logic.parsing.veriT

import scala.util.parsing.combinator._
import at.logic.language.fol._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import java.io.FileReader

object VeriTParser extends RegexParsers {

  def read(filename : String) : List[List[FOLFormula]] = {
    parse(finalResult, new FileReader(filename)) match {
      case Success(r, _) => r
      case Failure(msg, _) => throw new Exception("Failure in veriT parsing: " + msg)
      case Error(msg, _) => throw new Exception("Error in veriT parsing: " + msg)
    }
  }

  // Each list of formulas corresponds to the formulas occurring in one of the axioms.
  // TODO: process this?
  def finalResult : Parser[List[List[FOLFormula]]] = rep(line) ^^ {
    case list => list.filterNot(l => l.isEmpty)
  }
  
  def line : Parser[List[FOLFormula]] = useless | ruleDesc
  
  // For type-matching purposes...
  def useless : Parser[List[FOLFormula]] = (success | unsat | header) ^^ { 
    case s => Nil }
  
  // Dummy strings that should be ignored
  def success : Parser[String] = "success"
  def unsat : Parser[String] = "unsat"
  def header : Parser[String] = "verit dev - the VERI(T) theorem prover (UFRN/LORIA)."
  
  def ruleDesc : Parser[List[FOLFormula]] = "(set" ~ label ~ "(" ~> rule <~ "))"
  def label : Parser[String] = ".c" ~ """\d+""".r ^^ { case s1 ~ s2 => s1 ++ s2 }

  def rule : Parser[List[FOLFormula]] = axiom | innerRule
  
  def axiom : Parser[List[FOLFormula]] = input | eq_reflexive | eq_transitive | eq_congruence | eq_congruence_pred
  
  def input : Parser[List[FOLFormula]] = "input" ~> conclusion
  // TODO: process these formulas to obtain the terms
  def eq_reflexive : Parser[List[FOLFormula]] = "eq_reflexive" ~> conclusion
  def eq_transitive : Parser[List[FOLFormula]] = "eq_transitive" ~> conclusion
  def eq_congruence : Parser[List[FOLFormula]] = "eq_congruence" ~> conclusion
  def eq_congruence_pred : Parser[List[FOLFormula]] = "eq_congruence_pred" ~> conclusion

  def innerRule : Parser[List[FOLFormula]] = resolution | and | and_pos | or
  
  // Rules that I don't care
  def resolution : Parser[List[FOLFormula]] = "resolution" ~> premises <~ conclusion
  def and : Parser[List[FOLFormula]] = "and" ~> premises <~ conclusion
  // TODO: this rule has only conclusion, is it an axiom? Should I consider it??
  def and_pos : Parser[List[FOLFormula]] = "and_pos" ~> conclusion  ^^ { case _ => Nil }
  def or : Parser[List[FOLFormula]] = "or" ~> premises <~ conclusion
  
  // I don't care about premises. I only use the leaves
  def premises : Parser[List[FOLFormula]] = ":clauses (" ~ rep(label) ~ ")" ^^ { case _ => Nil}
  def conclusion : Parser[List[FOLFormula]] = ":conclusion (" ~> rep(formula) <~ ")"
 
  def formula : Parser[FOLFormula] = andFormula | orFormula | notFormula | pred // | eqFormula
  def term : Parser[FOLTerm] = name ~ rep(term) ^^ {
    case name ~ args => 
      val n = ConstantStringSymbol(name)
      Function(n, args)
  }

  def andFormula : Parser[FOLFormula] = "(and" ~> rep(formula) <~ ")" ^^ { 
    case flst => Utils.andN(flst) 
  }
  def orFormula : Parser[FOLFormula] = "(or" ~> rep(formula) <~ ")" ^^ { 
    case flst => Utils.orN(flst) 
  }
  // TODO: actually, equality is being parsed as a predicate. Check if this is enough.
  //def eqFormula : Parser[FOLFormula] = "(=" ~> term ~ term <~ ")" ^^ { 
  //  case t1 ~ t2 => println("Found equality formula with terms " + t1 + " and " + t2); Equation(t1, t2)
  //}
  def notFormula : Parser[FOLFormula] = "(not" ~> formula <~ ")" ^^ { 
    case f => Neg(f) 
  }
  def pred : Parser[FOLFormula] = "(" ~> name ~ rep(term) <~ ")" ^^ { 
    case name ~ args => 
      val n = ConstantStringSymbol(name)
      Atom(n, args) 
  }
  
  def name : Parser[String] = """[^ ():]+""".r

}
