package at.logic.transformations.ceres.autoprop

import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.base.{LKProof, Sequent}
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.language.hol.{HOLExpression, HOLFormula}
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.typedLambdaCalculus.Var
import at.logic.language.schema._
import at.logic.calculi.slk._
import at.logic.transformations.ceres.projections.printSchemaProof
import at.logic.transformations.ceres.unfolding.{StepMinusOne, SchemaSubstitution1}
import collection.immutable


// continue autopropositional
object Autoprop {
  // This method is used in prooftool to test autopropositional feature.
  def apply(): LKProof = apply(new FSequent(immutable.Seq[HOLFormula](), immutable.Seq[HOLFormula]()))

  def apply(seq: FSequent): LKProof = {
    if (isSeqTautology(seq)) {
      val (f, rest) = getAxiomfromSeq(seq)
      return WeakeningRuleN(Axiom(f::Nil, f::Nil), rest)
    }
    if (getNonAtomicFAnt(seq) != None) {
      val f = getNonAtomicFAnt(seq).get._1
      println("\nf = "+printSchemaProof.formulaToString(f) )
      val rest = getNonAtomicFAnt(seq).get._2
  //    println("\nrest = "+rest )

      f match {
        case Neg(f1) => return NegLeftRule(apply(new FSequent(rest.antecedent, f1 +: rest.succedent)), f1)
        case And(f1, f2) => {
          val up1 = AndLeft1Rule(apply(new FSequent(f1 +: f2 +: rest.antecedent, rest.succedent)), f1, f)
          val up2 = AndLeft2Rule(up1, f2, f)
          return WeakeningLeftRule(up2, f)
        }
        case Or(f1, f2) => {
          val t1 = apply(new FSequent(f1 +: rest.antecedent, rest.succedent))
          val t2 = apply(new FSequent(f2 +: rest.antecedent, rest.succedent))
          val up = OrLeftRule(t1, t2, f1, f2)
          return ContractionRuleN(up, rest)
        }
        case BigAnd(i, iter, from, to) => {
          val i = IntVar(new VariableStringSymbol("i"))
          if (from == to) {
            val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
            val subst = new SchemaSubstitution1[HOLExpression](new_map)
            return AndLeftEquivalenceRule3(apply(new FSequent(subst(iter).asInstanceOf[SchemaFormula] +: rest.antecedent, rest.succedent)), subst(iter).asInstanceOf[SchemaFormula], f.asInstanceOf[SchemaFormula])
          }
          else {
            println("to = "+to)
            val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
            val subst = new SchemaSubstitution1[HOLExpression](new_map)
            val up = AndLeftRule(apply(new FSequent(BigAnd(i, iter, from, Pred(to)) +: subst(iter).asInstanceOf[HOLFormula] +:  rest.antecedent, rest.succedent)), BigAnd(i, iter, from, Pred(to)), subst(iter).asInstanceOf[HOLFormula])
            return AndLeftEquivalenceRule1(up, And(BigAnd(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula]), BigAnd(i, iter, from, to))
          }
        }
        case BigOr(i, iter, from, to) => {
          val i = IntVar(new VariableStringSymbol("i"))
          if (from == to){
            val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
            val subst = new SchemaSubstitution1[HOLExpression](new_map)
            return OrLeftEquivalenceRule3(apply(new FSequent(subst(iter).asInstanceOf[SchemaFormula] +: rest.antecedent, rest.succedent)), subst(iter).asInstanceOf[SchemaFormula], f.asInstanceOf[SchemaFormula])
          }
          else {
            val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
            val subst = new SchemaSubstitution1[HOLExpression](new_map)
            val up = OrLeftRule(apply(new FSequent(BigOr(i, iter, from, Pred(to)) +:  rest.antecedent, rest.succedent)), apply(new FSequent(subst(iter).asInstanceOf[HOLFormula] +:  rest.antecedent, rest.succedent)), BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[HOLFormula])
            val up1 = ContractionRuleN(up, rest)
            return OrLeftEquivalenceRule1(up1, Or(BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula]), BigOr(i, iter, from, to))
          }
        }
        case _ => throw new Exception("Error in ANT-case in Autoprop.apply !\n")
      }
    }

    if (getNonAtomicFSucc(seq) == None)
      throw new Exception("\nError in Autoprop SUCC !\n")
    val f = getNonAtomicFSucc(seq).get._1
    println("\nf = "+printSchemaProof.formulaToString(f) )
    val rest = getNonAtomicFSucc(seq).get._2
    f match {
      case Neg(f1) => return NegRightRule(apply(new FSequent(f1 +: rest.antecedent, rest.succedent)), f1)
      case Or(f1, f2) => {
        val up1 = OrRight1Rule(apply(new FSequent(rest.antecedent, f1 +: f2 +: rest.succedent)), f1, f)
        val up2 = OrRight2Rule(up1, f2, f)
        return WeakeningRightRule(up2, f)
      }
      case And(f1, f2) => {
        val t1 = apply(new FSequent(rest.antecedent, f1 +: rest.succedent))
        val t2 = apply(new FSequent(rest.antecedent, f2 +: rest.succedent))
        val up = AndRightRule(t1, t2, f1, f2)
        return ContractionRuleN(up, rest)
      }
      case BigAnd(i, iter, from, to) => {
        val i = IntVar(new VariableStringSymbol("i"))
        if (from == to) {
          val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          return AndRightEquivalenceRule3(apply(new FSequent(rest.antecedent, subst(iter).asInstanceOf[SchemaFormula] +: rest.succedent)), subst(iter).asInstanceOf[SchemaFormula], f.asInstanceOf[SchemaFormula])
        }
        else {
          val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          val up = AndRightRule(apply(new FSequent(BigAnd(i, iter, from, Pred(to)) +: subst(iter).asInstanceOf[HOLFormula] +:  rest.antecedent, BigAnd(i, iter, from, Pred(to)) +: rest.succedent)), apply(new FSequent(rest.antecedent, subst(iter).asInstanceOf[HOLFormula] +: rest.succedent)), BigAnd(i, iter, from, Pred(to)), subst(iter).asInstanceOf[HOLFormula])
          val up1 = ContractionRuleN(up, rest)
          return AndRightEquivalenceRule1(up1, And(BigAnd(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula]), BigAnd(i, iter, from, to))
        }
      }
      case BigOr(i, iter, from, to) => {
        val i = IntVar(new VariableStringSymbol("i"))
        if (from == to){
          val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          return OrRightEquivalenceRule3(apply(new FSequent(subst(iter).asInstanceOf[SchemaFormula] +: rest.antecedent, rest.succedent)), subst(iter).asInstanceOf[SchemaFormula], f.asInstanceOf[SchemaFormula])
        }
        else {
          val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          val up = OrRightRule(apply(new FSequent(rest.antecedent, BigOr(i, iter, from, Pred(to)) +: subst(iter).asInstanceOf[HOLFormula] +: rest.succedent)), BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[HOLFormula])
          return OrRightEquivalenceRule1(up, Or(BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula]), BigOr(i, iter, from, to))
        }
      }
      case _ => throw new Exception("Error in SUCC-case in Autoprop.apply !\n")
    }
    Axiom(Nil,Nil)
  }

  def ContractionRuleN(p : LKProof, seq: FSequent) : LKProof = {
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
