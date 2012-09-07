package at.logic.algorithms.normalization

import at.logic.language.hol.HOLFormula

object NNF {
  def apply(f: HOLFormula) : HOLFormula = {
    //    println("\nf = "+printSchemaProof.formulaToString (f))
    f match {
      case at.logic.language.hol.Atom(_, _) => f
      case at.logic.language.hol.Imp(f1, f2) => apply(at.logic.language.hol.Or(at.logic.language.hol.Neg(f1), f2))
      case at.logic.language.hol.Neg(f1) => f1 match {
        case at.logic.language.hol.Atom(_, _) => f
        case at.logic.language.hol.Neg(f2) => apply(f2)
        case at.logic.language.hol.And(a,b) => at.logic.language.hol.Or(apply(at.logic.language.hol.Neg(a)), apply(at.logic.language.hol.Neg(b)))
        case at.logic.language.hol.Or(a,b) => at.logic.language.hol.And(apply(at.logic.language.hol.Neg(a)), apply(at.logic.language.hol.Neg(b)))
        case at.logic.language.hol.Imp(a, b) => apply(at.logic.language.hol.And(a, at.logic.language.hol.Neg(b)))
        case at.logic.language.hol.ExVar(x, f2) => at.logic.language.hol.AllVar(x, apply(at.logic.language.hol.Neg(f2)))
        case at.logic.language.hol.AllVar(x, f2) => at.logic.language.hol.ExVar(x, apply(at.logic.language.hol.Neg(f2)))
        case _ => throw new Exception("Error in Neg in NNF")
      }
      case at.logic.language.hol.And(f1, f2) => at.logic.language.hol.And(apply(f1), apply(f2))
      case at.logic.language.hol.Or(f1, f2) => at.logic.language.hol.Or(apply(f1), apply(f2))
      case at.logic.language.hol.ExVar(x, f1) => at.logic.language.hol.ExVar(x, apply(f1))
      case at.logic.language.hol.AllVar(x, f1) => at.logic.language.hol.AllVar(x, apply(f1))
      case _ => throw new Exception("Missing case in object NNF")
    }
  }
}