package at.logic.parsing.veriT

import at.logic.language.fol._
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols._
import at.logic.utils.latex._
import java.io._
import org.apache.commons.lang3.StringEscapeUtils
import at.logic.calculi.lk.base.FSequent
import at.logic.language.lambda.types.{Ti, To}


object VeriTExporter {

  // Takes a sequent and generates the input for VeriT as a string.
  def apply(s: FSequent, fileName: String) : File = {
    // Define the logic
    val logic = "(set-logic QF_UF)\n"
    // Declare the function and predicate symbols with arity
    val symbols = getSymbolsDeclaration((s._1 ++ s._2).asInstanceOf[List[FOLFormula]])
    // Generate assertions for the antecedent and succedent formulas
    val asserts = getAssertions(s._1.asInstanceOf[List[FOLFormula]], s._2.asInstanceOf[List[FOLFormula]])
    // Generate the check_sat formula
    val check_sat = "(check-sat)"

    // Writing to a file
    val file = new File(fileName)
    val fw = new FileWriter(file.getAbsoluteFile)
    val bw = new BufferedWriter(fw)
    bw.write( logic + symbols + asserts + check_sat )
    bw.close()

    file
  }

  private def getAssertions(ant: List[FOLFormula], succ: List[FOLFormula]) = { 
    val s1 = ant.foldLeft(""){ case (acc, f) =>
      "(assert " + toSMTFormat(f) + ")\n" + acc
    }
    
    if (succ.length == 0) {
      s1
    } else {
      val negs = succ.map(x => Neg(x))
      val disj = Or(negs)
      s1 + "(assert " + toSMTFormat(disj) + ")\n"
    }
  }
  
  // Gets all the symbols and arities that occur in the formulas of the list
  private def getSymbolsDeclaration(flst: List[FOLFormula]) = {
    val symbols = flst.foldLeft(Set[(String, Int, TA)]()) ( (acc, f) =>
      getSymbols(f) ++ acc
    )
    symbols.foldLeft("(declare-sort S 0)\n") { case (acc, t) => t._3 match {
      // It is an atom
      case To => acc ++ "(declare-fun " + toSMTString(t._1) + " (" + "S "*t._2 + ") Bool)\n"
      // It is a function
      case Ti => acc ++ "(declare-fun " + toSMTString(t._1) + " (" + "S "*t._2 + ") S)\n"
      case _ => throw new Exception("Unexpected type for function or predicate: " + t._3)
    }
    }
  }

  // TODO: Implement in hol/fol??
  // (Note: here we would only use propositional formulas, but it is already
  // implemented for quantifiers just in case...)
  private def getSymbols(f: FOLExpression) : Set[(String, Int, TA)] = f match {
    case FOLVar(s) => Set( (toSMTString(s), 0, Ti) )
    case FOLConst(s) => Set( (toSMTString(s), 0, Ti) )
    case Atom(pred, args) => 
      Set( (toSMTString(pred), args.size, f.exptype) ) ++ args.foldLeft(Set[(String, Int, TA)]())( (acc, f) => getSymbols(f) ++ acc)
    case Function(fun, args) => 
      Set( (toSMTString(fun), args.size, f.exptype) ) ++ args.foldLeft(Set[(String, Int, TA)]())( (acc, f) => getSymbols(f) ++ acc)
    case And(f1, f2) => getSymbols(f1) ++ getSymbols(f2)
    case Or(f1, f2) => getSymbols(f1) ++ getSymbols(f2)
    case Imp(f1, f2) => getSymbols(f1) ++ getSymbols(f2)
    case Neg(f1) => getSymbols(f1)
    case AllVar(_, f1) => getSymbols(f1)
    case ExVar(_, f1) => getSymbols(f1)
    case _ => throw new Exception("Undefined formula: " + f)
  }

  private def toSMTFormat(f: FOLExpression) : String = f match {
    case TopC => "true"
    case BottomC => "false"
    case FOLVar(s) => toSMTString (s)
    case FOLConst(s) => toSMTString (s)
    case Atom(pred, args) => 
      if (args.size == 0) {
        toSMTString (pred)
      } else {
        "(" + toSMTString (pred) + " " + args.foldLeft("")( (acc, t) => toSMTFormat(t) + " " + acc) + ")"
      }
    // Functions should have arguments.
    case Function(fun, args) => "(" + toSMTString (fun) + " " + args.foldRight("")( (t, acc) => toSMTFormat(t) + " " + acc) + ")"
    case And(f1, f2) => "(and " + toSMTFormat(f1) + " " + toSMTFormat(f2) + ")"
    case Or(f1, f2) => "(or " + toSMTFormat(f1) + " " + toSMTFormat(f2) + ")"
    case Imp(f1, f2) => "(=> " + toSMTFormat(f1) + " " + toSMTFormat(f2) + ")"
    case Neg(f1) => "(not " + toSMTFormat(f1) + ")"
    case _ => throw new Exception("Undefined formula for SMT: " + f)
  }

  // Note: not an exhaustive list
  private val smt_keywords = List(
    "set-logic", 
    "QF_UF", 
    "declare-sort", 
    "declare-fun", 
    "assert",
    "not", "and", "or",
    "as",
    "true", "false")

  // Transforms the string into ASCII and checks if 
  // it does not clash with veriT keywords.
  private def toSMTString(s: SymbolA) : String = toSMTString(s.toString)
  private def toSMTString(s: String) : String = {
      // It's a number, append a character before it.
      val ascii = if ( s.forall(c => Character.isDigit(c)) ) {
        "n" + s
      } 
      else {
        // Attempt #3
        StringEscapeUtils.escapeJava(s).replaceAll("""\\""", "")
      }

      if (smt_keywords.contains(ascii)) ascii + "_clash"
      else ascii
  }
}
