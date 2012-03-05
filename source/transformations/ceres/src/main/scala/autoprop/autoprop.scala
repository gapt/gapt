package at.logic.transformations.ceres.autoprop

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
import at.logic.language.hol.{HOLExpression, HOLFormula}
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.typedLambdaCalculus.Var
import at.logic.language.schema._
import at.logic.transformations.ceres.projections.printSchemaProof
import at.logic.transformations.ceres.unfolding.{StepMinusOne, SchemaSubstitution1}
import at.logic.utils.ds.trees.LeafTree
import collection.immutable


// continue autopropositional
object Autoprop {
  // This method is used in prooftool to test autopropositional feature.
  def apply(): LKProof = apply(test.apply())
  def apply(seq: FSequent): LKProof = {
    var p = apply1(seq)
    while (rulesNumber(p) != rulesNumber(StructuralOptimizationAfterAutoprop(p)))
      p = StructuralOptimizationAfterAutoprop(p)
    p
  }

  def apply1(seq: FSequent): LKProof = {
    if (isSeqTautology(seq)) {
      val (f, rest) = getAxiomfromSeq(seq)
      return WeakeningRuleN(Axiom(f::Nil, f::Nil), rest)
    }
    if (getNonAtomicFAnt(seq) != None) {
      val f = getNonAtomicFAnt(seq).get._1
//      println("\nf = "+printSchemaProof.formulaToString(f) )
      val rest = getNonAtomicFAnt(seq).get._2
  //    println("\nrest = "+rest )
      f match {
        case Neg(f1) => return NegLeftRule(apply1(new FSequent(rest.antecedent, f1 +: rest.succedent)), f1)
        case And(f1, f2) => {
          val up1 = AndLeft1Rule(apply1(new FSequent(f1 +: f2 +: rest.antecedent, rest.succedent)), f1, f)
          val up2 = AndLeft2Rule(up1, f2, f)
          return WeakeningLeftRule(up2, f)
        }
        case Or(f1, f2) => {
          val t1 = apply1(new FSequent(f1 +: rest.antecedent, rest.succedent))
          val t2 = apply1(new FSequent(f2 +: rest.antecedent, rest.succedent))
          val up = OrLeftRule(t1, t2, f1, f2)
          return ContractionRuleN(up, rest)
        }
        case BigAnd(i, iter, from, to) => {
          val i = IntVar(new VariableStringSymbol("i"))
          if (from == to) {
            val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
            val subst = new SchemaSubstitution1[HOLExpression](new_map)
            return AndLeftEquivalenceRule3(apply1(new FSequent(subst(iter).asInstanceOf[SchemaFormula] +: rest.antecedent, rest.succedent)), subst(iter).asInstanceOf[SchemaFormula], f.asInstanceOf[SchemaFormula])
          }
          else {
            val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
            val subst = new SchemaSubstitution1[HOLExpression](new_map)
            val up = AndLeftRule(apply1(new FSequent(BigAnd(i, iter, from, Pred(to)) +: subst(iter).asInstanceOf[HOLFormula] +:  rest.antecedent, rest.succedent)), BigAnd(i, iter, from, Pred(to)), subst(iter).asInstanceOf[HOLFormula])
            return AndLeftEquivalenceRule1(up, And(BigAnd(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula]), BigAnd(i, iter, from, to))
          }
        }
        case BigOr(i, iter, from, to) => {
          val i = IntVar(new VariableStringSymbol("i"))
          if (from == to){
            val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
            val subst = new SchemaSubstitution1[HOLExpression](new_map)
            return OrLeftEquivalenceRule3(apply1(new FSequent(subst(iter).asInstanceOf[SchemaFormula] +: rest.antecedent, rest.succedent)), subst(iter).asInstanceOf[SchemaFormula], f.asInstanceOf[SchemaFormula])
          }
          else {
            val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
            val subst = new SchemaSubstitution1[HOLExpression](new_map)
            val up = OrLeftRule(apply1(new FSequent(BigOr(i, iter, from, Pred(to)) +:  rest.antecedent, rest.succedent)), apply1(new FSequent(subst(iter).asInstanceOf[HOLFormula] +:  rest.antecedent, rest.succedent)), BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[HOLFormula])
            val up1 = ContractionRuleN(up, rest)
            return OrLeftEquivalenceRule1(up1, Or(BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula]), BigOr(i, iter, from, to))
          }
        }
        case _ => throw new Exception("Error in ANT-case in Autoprop.apply1 !\n")
      }
    }

    if (getNonAtomicFSucc(seq) == None)
      throw new Exception("\nError in Autoprop SUCC !\n")
    val f = getNonAtomicFSucc(seq).get._1
//    println("\nf = "+printSchemaProof.formulaToString(f) )
    val rest = getNonAtomicFSucc(seq).get._2
    f match {
      case Neg(f1) => return NegRightRule(apply1(new FSequent(f1 +: rest.antecedent, rest.succedent)), f1)
      case Or(f1, f2) => {
        val up1 = OrRight1Rule(apply1(new FSequent(rest.antecedent, f1 +: f2 +: rest.succedent)), f1, f)
        val up2 = OrRight2Rule(up1, f2, f)
        return WeakeningRightRule(up2, f)
      }
      case And(f1, f2) => {
        val t1 = apply1(new FSequent(rest.antecedent, f1 +: rest.succedent))
        val t2 = apply1(new FSequent(rest.antecedent, f2 +: rest.succedent))
        val up = AndRightRule(t1, t2, f1, f2)
        return ContractionRuleN(up, rest)
      }
      case BigAnd(i, iter, from, to) => {
        val i = IntVar(new VariableStringSymbol("i"))
        if (from == to) {
          val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          return AndRightEquivalenceRule3(apply1(new FSequent(rest.antecedent, subst(iter).asInstanceOf[SchemaFormula] +: rest.succedent)), subst(iter).asInstanceOf[SchemaFormula], f.asInstanceOf[SchemaFormula])
        }
        else {
          val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          val up = AndRightRule(apply1(new FSequent(rest.antecedent, BigAnd(i, iter, from, Pred(to)) +: rest.succedent)), apply1(new FSequent(rest.antecedent, subst(iter).asInstanceOf[HOLFormula] +: rest.succedent)), BigAnd(i, iter, from, Pred(to)), subst(iter).asInstanceOf[HOLFormula])
          val up1 = ContractionRuleN(up, rest)
          return AndRightEquivalenceRule1(up1, And(BigAnd(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula]), BigAnd(i, iter, from, to))
        }
      }
      case BigOr(i, iter, from, to) => {
        val i = IntVar(new VariableStringSymbol("i"))
        if (from == to){
          val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          return OrRightEquivalenceRule3(apply1(new FSequent(subst(iter).asInstanceOf[SchemaFormula] +: rest.antecedent, rest.succedent)), subst(iter).asInstanceOf[SchemaFormula], f.asInstanceOf[SchemaFormula])
        }
        else {
          val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          val up = OrRightRule(apply1(new FSequent(rest.antecedent, BigOr(i, iter, from, Pred(to)) +: subst(iter).asInstanceOf[HOLFormula] +: rest.succedent)), BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[HOLFormula])
          return OrRightEquivalenceRule1(up, Or(BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula]), BigOr(i, iter, from, to))
        }
      }
      case _ => throw new Exception("Error in SUCC-case in Autoprop.apply1 !\n")
    }
    throw new Exception("Error in Autoprop - missing case !")
  }

  def ContractionRuleN(p : LKProof, seq: FSequent) : LKProof = {
//    println("\nContrN proof:\n"+printSchemaProof(p))
    val up = seq.antecedent.foldLeft(p)((res, f) => ContractionLeftRule(res, f))
    seq.succedent.foldLeft(up)((res, f) => ContractionRightRule(res, f))
  }

  def WeakeningRuleN(p : LKProof, seq: FSequent) : LKProof = {
    val up = seq.antecedent.foldLeft(p)((res, f) => WeakeningLeftRule(res, f))
    seq.succedent.foldLeft(up)((res, f) => WeakeningRightRule(res, f))
  }

  //return the first non Atomic f-la and the subsequent without that f-la
  def getNonAtomicFAnt(seq: FSequent) : Option[(HOLFormula, FSequent)] = {
    seq.antecedent.foreach(f => f match {
      case IndexedPredicate(_, _) => {}
      case _ => return Some(f, removeFfromSeqAnt(seq, f))
    })
    None
  }

  def getNonAtomicFSucc(seq: FSequent) : Option[(HOLFormula, FSequent)] = {
    seq.succedent.foreach(f => f match {
      case IndexedPredicate(_, _) => {}
      case _ => return Some(f, removeFfromSeqSucc(seq, f))
    })
    None
  }
  
  def isAtom(f: HOLFormula): Boolean = f match {
    case IndexedPredicate(_, _) => true
    case _ => false
  }
  
  def isSeqTautology(seq: FSequent): Boolean = {
    seq.antecedent.foreach(f => seq.succedent.foreach(f2 =>  if(f == f2 && isAtom(f)) return true))
      return false
  }
  
  def removeFfromSeqAnt(seq: FSequent, f : HOLFormula) : FSequent = {
    new FSequent(seq.antecedent.filter(x => x != f) , seq.succedent)
  }

  def removeFfromSeqSucc(seq: FSequent, f : HOLFormula) : FSequent = {
    new FSequent(seq.antecedent, seq.succedent.filter(x => x != f))
  }

  def removeFfromSeqAnt(seq: FSequent, flist : List[HOLFormula]) : FSequent = {
    new FSequent(seq.antecedent.filter(x => !flist.contains(x)) , seq.succedent)
  }

  def removeFfromSeqSucc(seq: FSequent, flist : List[HOLFormula]) : FSequent = {
    new FSequent(seq.antecedent, seq.succedent.filter(x => !flist.contains(x)))
  }
  
  def getAxiomfromSeq(seq: FSequent) : (HOLFormula, FSequent) = {
    if (isSeqTautology(seq)) {
      seq.antecedent.foreach(f => if (seq.succedent.contains(f)){
        return (f, removeFfromSeqAnt(removeFfromSeqSucc(seq, f), f))
      })
      throw new Exception("\nError in if-autoprop.getAxiomfromSeq !\n")
    }
    else throw new Exception("\nError in else-autoprop.getAxiomfromSeq !\n")
  }
}


//delete from an SLKProof those weakening inefernces whose aux. f-las go to a contraction inference
object StructuralOptimizationAfterAutoprop {
  def apply(p: LKProof): LKProof = apply(p, p)
  def apply(p : LKProof, p_old : LKProof): LKProof = p match {
    case ax: NullaryLKProof => p
    case ContractionLeftRule(up, _, a1, a2, _)  => {
      val anc1 = getAncestors(a1);val anc2 = getAncestors(a2)
      val b1 = isDescentanfOfAuxFOccOfWeakRule(anc1, p_old)
      val b2 = isDescentanfOfAuxFOccOfWeakRule(anc2, p_old)
      if (b1 && b2)
        delSuperfluousRules(anc1 ++ anc2, up)
      else
        if (b1)
          delSuperfluousRules(anc1, up)
        else
          delSuperfluousRules(anc2, up)
    }
    case ContractionRightRule(up, _, a1, a2, _) => {
      val anc1 = getAncestors(a1);val anc2 = getAncestors(a2)
      val b1 = isDescentanfOfAuxFOccOfWeakRule(anc1, p_old)
      val b2 = isDescentanfOfAuxFOccOfWeakRule(anc2, p_old)
      if (b1 && b2)
        delSuperfluousRules(anc1 ++ anc2, up)
      else
        if (b1)
          delSuperfluousRules(anc1, up)
        else
          delSuperfluousRules(anc2, up)
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
        if (set.contains(a))
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

object test {
  def apply(): FSequent = {
    val k = IntVar(new VariableStringSymbol("k"))
    val real_n = IntVar(new VariableStringSymbol("n"))
    val n = k
    val n1 = Succ(k); val n2 = Succ(n1); val n3 = Succ(n2)
    val k1 = Succ(k); val k2 = Succ(n1); val k3 = Succ(n2)
    val s = Set[FormulaOccurrence]()

    val i = IntVar(new VariableStringSymbol("i"))
    val A = IndexedPredicate(new ConstantStringSymbol("A"), i)
    val B = IndexedPredicate(new ConstantStringSymbol("B"), i)
    val C = IndexedPredicate(new ConstantStringSymbol("C"), i)
    val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
    val four = Succ(three);val five = Succ(four); val six = Succ(Succ(four));val seven = Succ(Succ(five));       val A0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero())
    val A1 = IndexedPredicate(new ConstantStringSymbol("A"), one)
    val A2 = IndexedPredicate(new ConstantStringSymbol("A"), two)
    val A3 = IndexedPredicate(new ConstantStringSymbol("A"), three)

    val B0 = IndexedPredicate(new ConstantStringSymbol("B"), IntZero())

    val Ak = IndexedPredicate(new ConstantStringSymbol("A"), k)
    val Ai = IndexedPredicate(new ConstantStringSymbol("A"), i)
    val Ai1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(i))
    val orneg = at.logic.language.schema.Or(at.logic.language.schema.Neg(Ai).asInstanceOf[SchemaFormula], Ai1.asInstanceOf[SchemaFormula]).asInstanceOf[SchemaFormula]

    val Ak1 = IndexedPredicate(new ConstantStringSymbol("A"), Succ(k))
    val An = IndexedPredicate(new ConstantStringSymbol("A"), k)
    val An1 = IndexedPredicate(new ConstantStringSymbol("A"), n1)
    val An2 = IndexedPredicate(new ConstantStringSymbol("A"), n2)
    val An3 = IndexedPredicate(new ConstantStringSymbol("A"), n3)
    //             println("\n\n START \n\n")

    //      val fseq = FSequent(A0 :: Nil, A0 :: Nil)
    //      val fseq = FSequent(A0 :: Neg(A0) :: Nil, Nil)
    val biga = BigAnd(i, A, zero, two)
    val bigo = BigOr(i, A, zero, one)
    val biga2 = BigAnd(i, A, zero, two)
    val bigo2 = BigOr(i, A, zero, two)

    //      val fseq = FSequent(bigo :: Nil, A0 :: A1 :: Nil )
    //      val fseq = FSequent(biga :: Nil, A0 :: A1 :: Nil )
    //      val fseq = FSequent(biga :: Nil, A0 :: A1 :: A2 :: Nil )
    //      val fseq = FSequent(A :: B :: Nil, And(A, B) :: Nil)
//    val fseq = FSequent(A :: B :: C :: Nil, And(And(A, B), C) :: Nil)
//    val fseq = FSequent(bigo2 :: Nil, A0 :: A1 :: A2 :: Nil)
    val fseq = FSequent(A0 :: A1 :: A2 :: Nil, biga2 :: Nil)
//    val fseq = FSequent(A0 :: A1 :: A2 :: Nil, biga :: Nil)
    //      val fseq = FSequent(A0 :: A1 :: Nil, bigo :: Nil)
    fseq
  }
}
