package at.logic.algorithms.minimization

import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.calculi.slk._
import at.logic.calculi.slk.AndEquivalenceRule1._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.hol.{HOLExpression, HOLFormula}
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.typedLambdaCalculus.Var
import at.logic.language.schema._
import at.logic.parsing.language.simple.{SchemaSubstitution1, SHLK}
//import at.logic.transformations.ceres.unfolding.{SchemaSubstitution1, StepMinusOne}
import at.logic.utils.ds.trees.LeafTree
import collection.immutable
import at.logic.algorithms.lk.getAncestors


//delete from an SLKProof those weakening inefernces whose aux. f-las go to a contraction inference
object StructuralOptimizationAfterAutoprop {
  def apply(p: LKProof): LKProof = apply(p, p)

  def removeNonWeakDesc(anc: Set[FormulaOccurrence], ws: Set[FormulaOccurrence]): Set[FormulaOccurrence] = {
    anc.filter(fo => !(getAncestors(fo).intersect(ws)).isEmpty)
  }


  def apply(p : LKProof, p_old : LKProof): LKProof = p match {
    case ax: NullaryLKProof => p
    case ContractionLeftRule(up, _, a1, a2, _)  => {
      val anc1 = getAncestors(a1);val anc2 = getAncestors(a2)
      val b1 = isDescentanfOfAuxFOccOfWeakRule(anc1, p_old)
      val b2 = isDescentanfOfAuxFOccOfWeakRule(anc2, p_old)
      val wfo = getWeakFOccs(up)
      if ((b1 || b2) && isUpperMostContr(up)) {
        val p1 = delSuperfluousRules(removeNonWeakDesc(anc1 ++ anc2, wfo), up)

        //        println("\na1 = "+printSchemaProof.formulaToString (a1))
        //        println("\n1\n")
        //        println("\np1 = \n")
        //        println(printSchemaProof(p1))
        p1
      }
      else  {
        val p2 = apply(up, p_old)
        //        println("\n2 = \n")
        //        println("\na1 = "+printSchemaProof.formulaToString (a1.formula))

        //        println(printSchemaProof(p2))

        if (p2.root.antecedent.filter(fo => fo.formula == a1.formula).size < 2)
          return p2
        return ContractionLeftRule(p2, a1.formula)
      }
      //
      //      else
      //        if (b1) {
      //                    println("\n2 left\n")
      //          return delSuperfluousRules(removeNonWeakDesc(anc1, wfo), up)
      //        }
      //        else
      //          if (b2) {
      //                        println("\n3 left\n")
      //            delSuperfluousRules(removeNonWeakDesc(anc2, wfo), up)
      //          }
      //          else {
      //                        println("\n4 left\n")
      //            ContractionLeftRule(apply(up, p_old), a1.formula)
      //          }
    }
    case ContractionRightRule(up, _, a1, a2, _) => {
      val anc1 = getAncestors(a1);val anc2 = getAncestors(a2)
      val b1 = isDescentanfOfAuxFOccOfWeakRule(anc1, p_old)
      val b2 = isDescentanfOfAuxFOccOfWeakRule(anc2, p_old)
      val wfo = getWeakFOccs(p_old)
      if ((b1 || b2) && isUpperMostContr(up)) {
        //        println("\n1\n")
        val p1 = delSuperfluousRules(removeNonWeakDesc(anc1 ++ anc2, wfo), up)
        //        if (!removeNonWeakDesc(getAncestors(a1), wfo).isEmpty) {
        //          println("\n1 right if\n")
        p1
      }
      else {
        val p2 = apply(up, p_old)
        if (p2.root.succedent.filter(fo => fo.formula == a1.formula).size < 2)
          return p2
        return ContractionRightRule(p2, a1.formula)
      }
    }
    case AndLeftEquivalenceRule1(p, s, a, m) => {
      //            println("\nAndLeftEquivalenceRule1   YESSSSSSSSSSS \n")
      val new_p = apply(p, p_old)
      AndLeftEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
    }
    case AndRightEquivalenceRule1(p, s, a, m) => {
      // println("\nAndRightEquivalenceRule1\n")
      val new_p = apply(p, p_old)
      AndRightEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
    }
    case OrLeftEquivalenceRule1(p, s, a, m) => {
      val new_p = apply(p, p_old)
      OrLeftEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
    }
    case OrRightEquivalenceRule1(p, s, a, m) => {
      // println("\nOrRightEquivalenceRule1\n")
      val new_p = apply(p, p_old)
      OrRightEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
    }
    case AndLeftEquivalenceRule3(p, s, a, m) => {
      // println("\nAndLeftEquivalenceRule3\n")
      val new_p = apply(p, p_old)
      AndLeftEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
    }
    case AndRightEquivalenceRule3(p, s, a, m) => {
      // println("\nAndRightEquivalenceRule3\n")
      val new_p = apply(p, p_old)
      AndRightEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
    }
    case OrLeftEquivalenceRule3(p, s, a, m) => {
      val new_p = apply(p, p_old)
      OrLeftEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
    }
    case OrRightEquivalenceRule3(p, s, a, m) => {
      //println("\nOrRightEquivalenceRule3\n")
      val new_p = apply(p, p_old)
      OrRightEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
    }
    case WeakeningLeftRule(p, _, m) => {
      val new_p = apply(p, p_old)
      implicit val factory = defaultFormulaOccurrenceFactory
      WeakeningLeftRule( new_p, m.formula )
    }
    case WeakeningRightRule(p, _, m) => {
      val new_p = apply(p, p_old)
      implicit val factory = defaultFormulaOccurrenceFactory
      WeakeningRightRule( new_p, m.formula )
    }
    case OrLeftRule(p1, p2, _, a1, a2, m) => {
      val new_p1 = apply(p1, p_old)
      val new_p2 = apply(p2, p_old)
      OrLeftRule(new_p1, new_p2, a1.formula, a2.formula)
    }
    case AndRightRule(p1, p2, _, a1, a2, m) => {
      val new_p1 = apply(p1, p_old)
      val new_p2 = apply(p2, p_old)
      AndRightRule(new_p1, new_p2, a1.formula, a2.formula)
    }
    case NegLeftRule( p, _, a, m ) => {
      val new_p = apply(p, p_old)
      NegLeftRule( new_p, a.formula )
    }
    case AndLeft1Rule(p, r, a, m) =>  {
      val new_p = apply(p, p_old)
      val a2 = m.formula  match { case And(l, right) => right }
      //      println("AndLeft1Rule : "+printSchemaProof.sequentToString(new_p.root))
      //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
      //    println(printSchemaProof.formulaToString(a2))
      AndLeft1Rule( new_p, a.formula, a2)
    }
    case AndLeft2Rule(p, r, a, m) =>  {
      val new_p = apply(p, p_old)
      val a2 = m.formula  match { case And(l, _) => l }
      //     println("AndLeft2Rule : "+printSchemaProof.sequentToString(new_p.root))
      //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
      //     println(printSchemaProof.formulaToString(a2))
      AndLeft2Rule( new_p, a2, a.formula )
    }
    case OrRight1Rule(p, r, a, m) =>  {
      val new_p = apply(p, p_old)
      val a2 = m.formula  match { case Or(_, r) => r }
      //            println("\np or:r1 = "+p.root)
      //            println("\nnew_p or:r1 = "+new_p.root)
      //            println("\nor:r1 a = "+a.formula)
      //            println("\nor:r1 m = "+m.formula)
      OrRight1Rule( new_p, a.formula, a2)
    }
    case OrRight2Rule(p, r, a, m) =>  {
      val new_p = apply(p, p_old)
      val a2 = m.formula  match { case Or(l, _) => l }
      //            println("\np or:r2 = "+p.root)
      //            println("\nnew_p or:r2 = "+new_p.root)
      //          println("\nor:r2 a = "+a.formula)
      //            println("\nor:r2 m = "+m.formula)
      OrRight2Rule( new_p, a2, a.formula)
    }
    case NegRightRule( p, _, a, m ) => {
      val new_p = apply(p, p_old)
      NegRightRule( new_p, a.formula )
    }
    case _ => { println("ERROR in StructuralOptimizationAfterAutoprop : missing rule!");throw new Exception("ERROR in autoprop: StructuralOptimizationAfterAutoprop") }
  }
}


//**************************************************************************

//getDescOfAuxFOccOfWeakRule
object getWeakFOccs {
  def apply(p: LKProof): Set[FormulaOccurrence] = {
    p match {
      case ax: NullaryLKProof => return Set.empty[FormulaOccurrence]
      case WeakeningLeftRule(up, _, m) => {
        return apply(up) + m
      }
      case WeakeningRightRule(up, _, m) => {
        return apply(up) + m
      }
      case UnaryLKProof(_, up, _, _, _) => return apply(up)
      case BinaryLKProof(_, up1, up2, _, _, _, _) => return apply(up1) ++ apply (up2)
      case AndEquivalenceRule1(up, _, _, _) => return apply(up)
      case OrEquivalenceRule1(up, _, _, _) => return apply(up)
      case AndEquivalenceRule3(up, _, _, _) => return apply(up)
      case OrEquivalenceRule3(up, _, _, _) => return apply(up)
      case _ => { println("ERROR in getWeakFOccs : missing rule!");throw new Exception("ERROR in autoprop: getWeakFOccs") }
    }
  }
}

object isUpperMostContr {
  def apply(p: LKProof):Boolean = (contrNumber(p) == 0)

  def contrNumber(p: LKProof): Int = p match {
    case ax: NullaryLKProof => return 0
    case ContractionLeftRule(up, _, _, _, _) => return contrNumber(up) + 1
    case ContractionRightRule(up, _, _, _, _) =>return contrNumber(up) + 1
    case UnaryLKProof(_, up, _, _, _) => return contrNumber(up)
    case BinaryLKProof(_, up1, up2, _, _, _, _) => return contrNumber(up1) + contrNumber (up2)
    case AndEquivalenceRule1(up, _, _, _) => return contrNumber(up)
    case OrEquivalenceRule1(up, _, _, _) => return contrNumber(up)
    case AndEquivalenceRule3(up, _, _, _) => return contrNumber(up)
    case OrEquivalenceRule3(up, _, _, _) => return contrNumber(up)
    case _ => { println("ERROR in getWeakFOccs : missing rule!");throw new Exception("ERROR in autoprop: getWeakFOccs") }
  }
}


object isDescentanfOfAuxFOccOfWeakRule {
  def apply(s: Set[FormulaOccurrence], p:LKProof): Boolean = {
    //    println("\nrule = "+p.name)
    p match {
      case ax: NullaryLKProof => false
      case WeakeningLeftRule(up, _, m) => {
        if (s.contains(m))
          true
        else
          apply(s, up)
      }
      case WeakeningRightRule(up, _, m) => {
        if (s.contains(m))
          true
        else
          apply(s, up)
      }
      case UnaryLKProof(_, up, _, _, _) => apply(s, up)
      case BinaryLKProof(_, up1, up2, _, _, _, _) => apply(s, up1) || apply (s, up2)
      case AndEquivalenceRule1(up, _, _, _) => apply(s, up)
      case OrEquivalenceRule1(up, _, _, _) => apply(s, up)
      case AndEquivalenceRule3(up, _, _, _) => apply(s, up)
      case OrEquivalenceRule3(up, _, _, _) => apply(s, up)
      case _ => { println("ERROR in isDescentanfOfAuxFOccOfWeakRule : missing rule!");throw new Exception("ERROR in autoprop: StructuralOptimizationAfterAutoprop") }
    }
  }
}


// *************************************************************************
object delSuperfluousRules {
  def apply(set: Set[FormulaOccurrence], p_old: LKProof): LKProof = {
    //    println("\n\ndelSuperfluousWeakening  -  "+p_old.name)
    p_old match {
      case ax: NullaryLKProof => p_old
      case AndLeftEquivalenceRule1(p, s, a, m) => {
        val new_p = apply(set, p)
        AndLeftEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }
      case AndRightEquivalenceRule1(p, s, a, m) => {
        // println("\nAndRightEquivalenceRule1\n")
        val new_p = apply(set, p)
        AndRightEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }
      case OrRightEquivalenceRule1(p, s, a, m) => {
        // println("\nOrRightEquivalenceRule1\n")
        val new_p = apply(set, p)
        OrRightEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }
      case OrLeftEquivalenceRule1(p, s, a, m) => {
        val new_p = apply(set, p)
        OrLeftEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }
      case AndLeftEquivalenceRule3(p, s, a, m) => {
        // println("\nAndLeftEquivalenceRule3\n")
        val new_p = apply(set, p)
        AndLeftEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }
      case AndRightEquivalenceRule3(p, s, a, m) => {
        // println("\nAndRightEquivalenceRule3\n")
        val new_p = apply(set, p)
        AndRightEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }
      case OrLeftEquivalenceRule3(p, s, a, m) => {
        //println("\nOrLeftEquivalenceRule3\n")
        val new_p = apply(set, p)
        OrLeftEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }
      case OrRightEquivalenceRule3(p, s, a, m) => {
        //println("\nOrRightEquivalenceRule3\n")
        val new_p = apply(set, p)
        OrRightEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }
      case WeakeningLeftRule(p, _, m) => {
        if (set.contains(m))
          return apply(set, p)
        val new_p = apply(set, p)
        implicit val factory = defaultFormulaOccurrenceFactory
        WeakeningLeftRule( new_p, m.formula )
      }
      case WeakeningRightRule(p, _, m) => {
        if (set.contains(m))
          return apply(set, p)
        val new_p = apply(set, p)
        implicit val factory = defaultFormulaOccurrenceFactory
        WeakeningRightRule( new_p, m.formula )
      }
      case OrLeftRule(p1, p2, _, a1, a2, m) => {
        if (set.contains(a1))
          return apply(set, p2)
        if (set.contains(a2))
          return apply(set, p1)
        val new_p1 = apply(set, p1)
        val new_p2 = apply(set, p2)
        OrLeftRule(new_p1, new_p2, a1.formula, a2.formula)
      }
      case AndRightRule(p1, p2, _, a1, a2, m) => {
        if (set.contains(a1))
          return apply(set, p2)
        if (set.contains(a2))
          return apply(set, p1)
        val new_p1 = apply(set, p1)
        val new_p2 = apply(set, p2)
        AndRightRule(new_p1, new_p2, a1.formula, a2.formula)
      }
      case NegLeftRule( p, _, a, m ) => {
        if (set.contains(a))
          return apply(set, p)
        val new_p = apply(set, p)
        NegLeftRule( new_p, a.formula )
      }
      case AndLeft1Rule(p, r, a, m) =>  {
        if (set.contains(a))
          return apply(set, p)
        val new_p = apply(set, p)
        val a2 = m.formula  match { case And(l, right) => right }
        //      println("AndLeft1Rule : "+printSchemaProof.sequentToString(new_p.root))
        //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
        //    println(printSchemaProof.formulaToString(a2))
        AndLeft1Rule( new_p, a.formula, a2)
      }
      case AndLeft2Rule(p, r, a, m) =>  {
        if (set.contains(m))
          return apply(set, p)
        val new_p = apply(set, p)
        val a2 = m.formula  match { case And(l, _) => l }
        //     println("AndLeft2Rule : "+printSchemaProof.sequentToString(new_p.root))
        //     println("aux : \n"+printSchemaProof.formulaToString(a.formula))
        //     println(printSchemaProof.formulaToString(a2))
        AndLeft2Rule( new_p, a2, a.formula )
      }
      case OrRight1Rule(p, r, a, m) =>  {
        if (set.contains(m))
          return apply(set, p)
        val new_p = apply(set, p)
        val a2 = m.formula  match { case Or(_, r) => r }
        //            println("\np or:r1 = "+p.root)
        //            println("\nnew_p or:r1 = "+new_p.root)
        //            println("\nor:r1 a = "+a.formula)
        //            println("\nor:r1 m = "+m.formula)
        OrRight1Rule( new_p, a.formula, a2)
      }
      case OrRight2Rule(p, r, a, m) =>  {
        if (set.contains(m))
          return apply(set, p)
        val new_p = apply(set, p)
        val a2 = m.formula  match { case Or(l, _) => l }
        //            println("\np or:r2 = "+p.root)
        //            println("\nnew_p or:r2 = "+new_p.root)
        //          println("\nor:r2 a = "+a.formula)
        //            println("\nor:r2 m = "+m.formula)
        OrRight2Rule( new_p, a2, a.formula)
      }
      case NegRightRule( p, _, a, m ) => {
        if (set.contains(a))
          return apply(set, p)
        val new_p = apply(set, p)
        NegRightRule( new_p, a.formula )
      }
      case ContractionLeftRule(p, _, a1, a2, m) => {
        if (set.contains(m))
          return apply(set, p)
        val new_p = apply(set, p)
        ContractionLeftRule( new_p, a1.formula )
      }
      case ContractionRightRule(p, _, a1, a2, m) => {
        if (set.contains(m))
          return apply(set, p)
        val new_p = apply(set, p)
        //            println("\nc:r = "+new_p.root)
        ContractionRightRule( new_p, a1.formula )
      }
      case _ => { println("ERROR in delSuperfluousWeakening : missing rule!");throw new Exception("ERROR in delSuperfluousWeakening") }
    }
  }
}

//**************************************************************************
object rulesNumber {
  def apply(p: LKProof) : Int = p match {
    case ax: NullaryLKProof  => 0
    case BinaryLKProof(_, p1, p2, _, _, _, _) => apply(p1) + apply(p2) + 1
    case UnaryLKProof(_, p, _, _, _) => apply(p) + 1
    case AndEquivalenceRule1(up, _, _, _) => apply(up) + 1
    case OrEquivalenceRule1(up, _, _, _) => apply(up) + 1
    case AndEquivalenceRule3(up, _, _, _) => apply(up) + 1
    case OrEquivalenceRule3(up, _, _, _) => apply(up) + 1
    case _ => { println("ERROR in delSuperfluousWeakening : missing rule!");throw new Exception("ERROR in rulesNumber") }
  }
}


