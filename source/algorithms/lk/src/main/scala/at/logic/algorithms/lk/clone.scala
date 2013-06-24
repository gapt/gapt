package at.logic.algorithms.lk

import at.logic.calculi.lk.base.LKProof
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.occurrences.defaultFormulaOccurrenceFactory
import at.logic.calculi.slk._
import at.logic.language.schema.SchemaFormula
import at.logic.calculi.lk.equationalRules.{EquationRight2Rule, EquationRight1Rule, EquationLeft2Rule, EquationLeft1Rule}
import at.logic.calculi.lk.definitionRules.{DefinitionRightRule, DefinitionLeftRule}

//creates a copy of an existing LK proof (used for unfolding, not to have cycles in the tree having the base proof several times)
object CloneLKProof {
  import at.logic.language.hol._

  def apply(p: LKProof):LKProof = {
    //      println("\nCloneLKProof : "+p.rule)
    p match {

      case Axiom(ro) => Axiom(ro.antecedent.map(fo => fo.formula.asInstanceOf[HOLFormula]),ro.succedent.map(fo => fo.formula.asInstanceOf[HOLFormula]))

      case AndLeftEquivalenceRule1(p, s, a, m) => {
        //            println("\nAndLeftEquivalenceRule1   YESSSSSSSSSSS \n")
        val new_p = apply(p)
        AndLeftEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }

      case AndRightEquivalenceRule1(p, s, a, m) => {
        // println("\nAndRightEquivalenceRule1\n")
        val new_p = apply(p)
        AndRightEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }

      case OrRightEquivalenceRule1(p, s, a, m) => {
        // println("\nOrRightEquivalenceRule1\n")
        val new_p = apply(p)
        OrRightEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }

      case AndLeftEquivalenceRule3(p, s, a, m) => {
        // println("\nAndLeftEquivalenceRule3\n")
        val new_p = apply(p)
        AndLeftEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }

      case AndRightEquivalenceRule3(p, s, a, m) => {
        // println("\nAndRightEquivalenceRule3\n")
        val new_p = apply(p)
        AndRightEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }

      case OrRightEquivalenceRule3(p, s, a, m) => {
        //println("\nOrRightEquivalenceRule3\n")
        val new_p = apply(p)
        OrRightEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }

      case WeakeningLeftRule(p, _, m) => {
        val new_p = apply(p)
        implicit val factory = defaultFormulaOccurrenceFactory
        WeakeningLeftRule( new_p, m.formula )
      }

      case WeakeningRightRule(p, _, m) => {
        val new_p = apply(p)
        implicit val factory = defaultFormulaOccurrenceFactory
        WeakeningRightRule( new_p, m.formula )
      }

      case CutRule( p1, p2, _, a1, a2 ) => {
        val new_p1 = apply(p1)
        val new_p2 = apply(p2)
        CutRule(new_p1, new_p2, a2.formula)
      }

      case OrLeftRule(p1, p2, _, a1, a2, m) => {
        val new_p1 = apply(p1)
        val new_p2 = apply(p2)
        OrLeftRule(new_p1, new_p2, a1.formula, a2.formula)
      }

      case AndRightRule(p1, p2, _, a1, a2, m) => {
        val new_p1 = apply(p1)
        val new_p2 = apply(p2)
        AndRightRule(new_p1, new_p2, a1.formula, a2.formula)
      }

      case NegLeftRule( p, _, a, m ) => {
        val new_p = apply(p)
        NegLeftRule( new_p, a.formula )
      }

      case AndLeft1Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case And(l, right) => right }
        //      println("AndLeft1Rule : "+printSchemaProof.sequentToString(new_p.root))
        //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
        //    println(printSchemaProof.formulaToString(a2))
        AndLeft1Rule( new_p, a.formula, a2)
      }

      case AndLeft2Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case And(l, _) => l }
        //     println("AndLeft2Rule : "+printSchemaProof.sequentToString(new_p.root))
        //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
        //     println(printSchemaProof.formulaToString(a2))
        AndLeft2Rule( new_p, a2, a.formula )
      }

      case OrRight1Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case Or(_, r) => r }
        //            println("\np or:r1 = "+p.root)
        //            println("\nnew_p or:r1 = "+new_p.root)
        //            println("\nor:r1 a = "+a.formula)
        //            println("\nor:r1 m = "+m.formula)
        OrRight1Rule( new_p, a.formula, a2)
      }

      case OrRight2Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case Or(l, _) => l }
        //            println("\np or:r2 = "+p.root)
        //            println("\nnew_p or:r2 = "+new_p.root)
        //          println("\nor:r2 a = "+a.formula)
        //            println("\nor:r2 m = "+m.formula)
        OrRight2Rule( new_p, a2, a.formula)
      }

      case NegRightRule( p, _, a, m ) => {
        val new_p = apply(p)
        NegRightRule( new_p, a.formula )
      }

      case ContractionLeftRule(p, _, a1, a2, m) => {
        val new_p = apply(p)
        ContractionLeftRule( new_p, a1.formula )
      }

      case ContractionRightRule(p, _, a1, a2, m) => {
        val new_p = apply(p)
        //            println("\nc:r = "+new_p.root)
        ContractionRightRule( new_p, a1.formula )
      }

      case ImpLeftRule(p1, p2, _, a1, a2, m) => {
        val new_p1 = apply(p1)
        val new_p2 = apply(p2)
        ImpLeftRule(new_p1, new_p2, a1.formula, a2.formula)
      }

      case ImpRightRule(p, _, a1, a2, m) => {
        val new_p = apply(p)
        ImpRightRule(new_p, a1.formula, a2.formula)
      }

      case EquationLeft1Rule(up1, up2, _, eqocc, auxocc, prin) => {
        val new_p1 = apply(up1)
        val new_p2 = apply(up2)
        EquationLeft1Rule(new_p1, new_p2, eqocc.formula, auxocc.formula, prin.formula)
      }

      case EquationLeft2Rule(up1, up2, _, eqocc, auxocc, prin) => {
        val new_p1 = apply(up1)
        val new_p2 = apply(up2)
        EquationLeft2Rule(new_p1, new_p2, eqocc.formula, auxocc.formula, prin.formula)
      }

      case EquationRight1Rule(up1, up2, _, eqocc, auxocc, prin) => {
        val new_p1 = apply(up1)
        val new_p2 = apply(up2)
        EquationRight1Rule(new_p1, new_p2, eqocc.formula, auxocc.formula, prin.formula)
      }

      case EquationRight2Rule(up1, up2, _, eqocc, auxocc, prin) => {
        val new_p1 = apply(up1)
        val new_p2 = apply(up2)
        EquationRight2Rule(new_p1, new_p2, eqocc.formula, auxocc.formula, prin.formula)
      }

      case DefinitionLeftRule(up, _, aux, prin) => {
        val new_p = apply(up)
        DefinitionLeftRule(new_p, aux.formula, prin.formula)
      }

      case DefinitionRightRule(up, _, aux, prin) => {
        val new_p = apply(up)
        DefinitionRightRule(new_p, aux.formula, prin.formula)
      }
      case u => throw new UnfoldException("Rule is not supported: " + u.rule)
    }}
}

class UnfoldException(msg: String) extends Exception(msg)
