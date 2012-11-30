package at.logic.transformations.ceres.ACNF

import at.logic.algorithms.lk.getAncestors
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.calculi.slk._
import at.logic.calculi.slk.AndEquivalenceRule1._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.algorithms.shlk._
import at.logic.utils.ds.trees.LeafTree
import collection.immutable
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols.{ConstantSymbolA, ConstantStringSymbol}
import at.logic.language.lambda.typedLambdaCalculus.{AppN, LambdaExpression, Var}
import at.logic.language.lambda.types.FunctionType._
import at.logic.language.lambda.types.To._
import at.logic.language.lambda.types._
import at.logic.language.hol.Atom._
import at.logic.language.schema.foTerm._
import at.logic.language.schema._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._

  object acnf {
    def apply(resRefutation: LKProof, groun_proj_set: Set[LKProof]): LKProof = {
      resRefutation match {
        case Axiom(seq) => {
          if(seq.antecedent.isEmpty) {
            groun_proj_set.filter(p => p.root.succedent.map(fo => fo.formula).intersect(seq.succedent.map(fo => fo.formula)).nonEmpty).head
          }
          else
            if(seq.succedent.isEmpty) {
              groun_proj_set.filter(p => p.root.antecedent.map(fo => fo.formula).intersect(seq.antecedent.map(fo => fo.formula)).nonEmpty).head
            }
            else {
              groun_proj_set.filter(p => p.root.antecedent.map(fo => fo.formula).intersect(seq.antecedent.map(fo => fo.formula)).nonEmpty && p.root.succedent.map(fo => fo.formula).intersect(seq.succedent.map(fo => fo.formula)).nonEmpty).head
            }
        }
        case CutRule(up1, up2, _, a1, a2) => CutRule(apply(up1, groun_proj_set), apply(up2, groun_proj_set), a1.formula)
        case _ => throw new Exception("\nMissing case in acnf !\n")
      }
    }
  }
