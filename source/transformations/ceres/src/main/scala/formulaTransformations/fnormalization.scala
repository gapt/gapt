package at.logic.transformations.ceres.fnormalization

import at.logic.algorithms.lk.getAncestors
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.calculi.slk._
import at.logic.calculi.slk.AndEquivalenceRule1._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.hol.{ExVar, HOLExpression, HOLFormula}
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.typedLambdaCalculus.Var
import at.logic.language.schema._
import at.logic.transformations.ceres.projections.printSchemaProof
import at.logic.transformations.ceres.unfolding.{StepMinusOne, SchemaSubstitution1}

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
        case at.logic.language.hol.ExVar(x, f2) => at.logic.language.hol.AllVar(x, apply(f2))
        case at.logic.language.hol.AllVar(x, f2) => at.logic.language.hol.ExVar(x, apply(f2))
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