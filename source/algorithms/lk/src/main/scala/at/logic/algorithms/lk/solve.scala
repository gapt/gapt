package at.logic.algorithms.lk

import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.calculi.slk._
import at.logic.calculi.expansionTrees.{ExpansionTree, ExpansionSequent}
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.typedLambdaCalculus.{VariantGenerator, VariableNameGenerator, Var}
import at.logic.language.schema._
import at.logic.language.hol.{HOLConst, Atom, HOLExpression, HOLFormula, AllVar, ExVar}
import at.logic.language.lambda.types.{Ti, Tindex}
import at.logic.language.lambda.substitutions.Substitution
import at.logic.calculi.lk.quantificationRules._
import at.logic.provers.Prover
import at.logic.calculi.lk.equationalRules.{EquationRight1Rule, EquationRight2Rule, EquationLeft2Rule, EquationLeft1Rule}
import at.logic.calculi.lk.definitionRules.{DefinitionRightRule, DefinitionLeftRule}


/**
 * Constructs proofs sequents. Currently supports propositional logic as well as proof construction using expansion trees.
 */
object solve extends at.logic.utils.logging.Logger {

  /**
   * Main method for solving propositional sequents
   * @param seq: sequent to proof
   * @param cleanStructuralRules: whether to remove unnecessary structural rules
   * @return a proof if there is one
   */
  def solvePropositional( seq: FSequent, cleanStructuralRules: Boolean = true ): Option[LKProof] = {
     debug( "running solvePropositional" )

    val seq_norm = FSequent( seq.antecedent.toSet.toList, seq.succedent.toSet.toList )
    prove( seq_norm, new PropositionalProofStrategy ) match {
      case Some( p ) => {
        debug( "finished solvePropositional successfully" )
        //debug("# of contraction left rules: " + statistics.contLeftNumber(p))
        //debug("# of contraction right rules: " + statistics.contRightNumber(p))
        //debug("# of rules: " + statistics.rulesNumber(p))
        val pWithWeakening = addWeakenings( p, seq )
        if (cleanStructuralRules) {
          Some(CleanStructuralRules( pWithWeakening ))
        } else {
          Some( pWithWeakening )
        }
      }
      case None => {
        debug( "finished solvePropositional unsuccessfully" )
        None
      }
    }
  }

  private def prove(seq: FSequent, strategy: ProofStrategy): Option[LKProof] = {
    val ant_set = seq.antecedent.toSet
    val suc_set = seq.succedent.toSet
    if (( ant_set.size != seq.antecedent.size ) || ( suc_set.size != seq.succedent.size )) {
      // NOTE: this should never happen, apply* ensures that initial goal sequent is set-normalized,
      //       and prove preserves the property of being set-normalized.
      warn( "proving a sequent which is not set-normalized" )
      /*
      warn( "antecedent size (list): " + seq.antecedent.size )
      warn( "antecedent size (set): " + ant_set.size )
      warn( "succedent size (list): " + seq.succedent.size )
      warn( "succedent size (set): " + suc_set.size )
      warn( seq.toString )
      */
    }

    trace("proving: "+seq)

    if (SolveUtils.isAxiom(seq)) {
      val (f, rest) = SolveUtils.getAxiomfromSeq(seq)
      val p = addWeakenings(Axiom(f::Nil, f::Nil), seq)
      Some(p)
    } else if (SolveUtils.findNonschematicAxiom(seq).isDefined) {
      val Some((f,g)) = SolveUtils.findNonschematicAxiom(seq)
      Some(AtomicExpansion(seq,f,g))
    }
    // If all atoms are different, return None.
    else if(SolveUtils.noCommonAtoms(seq)) {
      None
    }
    else {

      // main step: ask strategy what to do
      val action = strategy.calcNextStep(seq)
      // TODO: next strategies are different for ETs

      trace("strategy has selected: " + action.formula)

      // dumbly apply whatever rule matches to this formula
      action.loc match {
        case ProofStrategy.FormulaLocation.Antecedent =>
          assert(seq.antecedent.contains(action.formula))
          applyActionAntecedent(action, seq, strategy)

        case ProofStrategy.FormulaLocation.Succedent =>
          assert(seq.succedent.contains(action.formula))
          applyActionSuccedent(action, seq, strategy)
      }
    }
  }


  private def applyActionAntecedent(action: ProofStrategy.Action, seq: FSequent, strategy: ProofStrategy): Option[LKProof] = {
    val rest = FSequent(seq.antecedent.diff(action.formula :: Nil), seq.succedent)

    action.formula match {

      // Unary Rules

      case Neg(f1) =>
        // If the auxiliary formulas already exists, no need to apply the rule
        if (SolveUtils.checkDuplicate(Nil, f1.asInstanceOf[HOLFormula] :: Nil, seq)) {
          // either return None if prove returns None, else weaken formula
          prove(rest, strategy).map(WeakeningLeftRule(_, action.formula))
        } else {
          // Computing premise antecedent and succedent
          val p_ant = rest.antecedent
          val p_suc = f1.asInstanceOf[HOLFormula] +: rest.succedent
          val premise = FSequent(p_ant, p_suc)
          prove(premise, strategy) match {
            case Some(p) => Some(NegLeftRule(p, f1.asInstanceOf[HOLFormula]))
            case None => None
          }
        }

      // Binary Rules

      case And(f1, f2) =>
        // same as above
        if (SolveUtils.checkDuplicate(f1.asInstanceOf[HOLFormula] :: f2.asInstanceOf[HOLFormula] :: Nil, Nil, seq)) {
          prove(rest, strategy).map(WeakeningLeftRule(_, action.formula))
        }
        // If one formula is there, do not contract, just pick the other.
        else if (SolveUtils.checkDuplicate(f1.asInstanceOf[HOLFormula] :: Nil, Nil, seq)) {
          val up_ant = f2.asInstanceOf[HOLFormula] +: rest.antecedent
          val up_suc = rest.succedent
          val upremise = FSequent(up_ant, up_suc)
          prove(upremise, strategy) match {
            case Some(proof) =>
              val proof_and2 = AndLeft2Rule(proof, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
              Some(proof_and2)
            case None => None
          }
        }
        else if (SolveUtils.checkDuplicate(f2.asInstanceOf[HOLFormula] :: Nil, Nil, seq)) {
          val up_ant = f1.asInstanceOf[HOLFormula] +: rest.antecedent
          val up_suc = rest.succedent
          val upremise = FSequent(up_ant, up_suc)
          prove(upremise, strategy) match {
            case Some(proof) =>
              val proof_and1 = AndLeft1Rule(proof, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
              Some(proof_and1)
            case None => None
          }
        }
        else {
          // For this case, contract the formula and choose the first and then the second conjunct
          val up_ant = f1.asInstanceOf[HOLFormula] +: f2.asInstanceOf[HOLFormula] +: rest.antecedent
          val up_suc = rest.succedent
          val upremise = FSequent(up_ant, up_suc)
          prove(upremise, strategy) match {
            case Some(proof) =>
              val proof_and2 = AndLeft2Rule(proof, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
              val proof_and1 = AndLeft1Rule(proof_and2, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
              val proof_contr = ContractionLeftRule(proof_and1, action.formula)
              Some(proof_contr)
            case None => None
          }
        } // end of And


      case Imp(f1, f2) =>
        // see above
        if (SolveUtils.checkDuplicate(f2.asInstanceOf[HOLFormula] :: Nil, Nil, seq) || SolveUtils.checkDuplicate(Nil, f1.asInstanceOf[HOLFormula] :: Nil, seq)) {
          prove(rest, strategy).map(WeakeningLeftRule(_, action.formula))
        } else {
          val p_ant1 = rest.antecedent
          val p_suc1 = f1.asInstanceOf[HOLFormula] +: rest.succedent
          val p_ant2 = f2.asInstanceOf[HOLFormula] +: rest.antecedent
          val p_suc2 = rest.succedent
          val premise1 = FSequent(p_ant1, p_suc1)
          val premise2 = FSequent(p_ant2, p_suc2)
          prove(premise1, strategy) match {
            case Some(p1) => prove(premise2, strategy) match {
              case Some(p2) =>
                val p = ImpLeftRule(p1, p2, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
                val p_contr = addContractions(p, seq)
                Some(p_contr)
              case None => None
            }
            case None => None
          }
        } // end of Imp


      case Or(f1, f2) =>
        // If the auxiliary formulas already exists, no need to apply the rule
        if (SolveUtils.checkDuplicate(f1.asInstanceOf[HOLFormula] :: Nil, Nil, seq) || SolveUtils.checkDuplicate(f2.asInstanceOf[HOLFormula] :: Nil, Nil, seq)) {
          prove(rest, strategy).map(WeakeningLeftRule(_, action.formula))
        } else {
          val p_ant1 = f1.asInstanceOf[HOLFormula] +: rest.antecedent
          val p_suc1 = rest.succedent
          val p_ant2 = f2.asInstanceOf[HOLFormula] +: rest.antecedent
          val p_suc2 = rest.succedent
          val premise1 = FSequent(p_ant1, p_suc1)
          val premise2 = FSequent(p_ant2, p_suc2)
          prove(premise2, strategy) match {
            case Some(p2) => prove(premise1, strategy) match {
              case Some(p1) =>
                val p = OrLeftRule(p1, p2, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
                val p_contr = addContractions(p, seq)
                Some(p_contr)
              case None => None
            }
            case None => None
          }
        } // end of Or


      // Schematic Rules

      case BigAnd(i, iter, from, to) =>
        val i = IntVar(new VariableStringSymbol("i"))
        if (from == to) {
          val new_map = Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          val sf = subst(iter).asInstanceOf[SchemaFormula]
          val p_ant = sf +: rest.antecedent
          val p_suc = rest.succedent
          val premise = FSequent(p_ant, p_suc)
          prove(premise, strategy) match {
            case Some(proof) =>
              val proof2 = AndLeftEquivalenceRule3(proof, sf, action.formula.asInstanceOf[SchemaFormula])
              Some(proof2)
            case None => None
          }
        }
        else {
          val new_map = Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          val sf1 = BigAnd(i, iter, from, Pred(to))
          val sf2 = subst(iter).asInstanceOf[HOLFormula]
          val p_ant = sf1 +: sf2 +: rest.antecedent
          val p_suc = rest.succedent
          val premise = FSequent(p_ant, p_suc)
          prove(premise, strategy) match {
            case Some(proof) =>
              val proof1 = AndLeftRule(proof, sf1, sf2)
              val and = And(BigAnd(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula])
              val proof2 = AndLeftEquivalenceRule1(proof1, and, BigAnd(i, iter, from, to))
              Some(proof2)
            case None => None
          }
        } // end of BigAnd

      case BigOr(i, iter, from, to) =>
        val i = IntVar(new VariableStringSymbol("i"))
        if (from == to) {
          val new_map = Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          val sf = subst(iter).asInstanceOf[SchemaFormula]
          val p_ant = sf +: rest.antecedent
          val p_suc = rest.succedent
          val premise = FSequent(p_ant, p_suc)
          prove(premise, strategy) match {
            case Some(proof) =>
              val proof1 = OrLeftEquivalenceRule3(proof, sf, action.formula.asInstanceOf[SchemaFormula])
              Some(proof1)
            case None => None
          }
        }
        else {
          val new_map = Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          val p_ant1 = BigOr(i, iter, from, Pred(to)) +: rest.antecedent
          val p_suc1 = rest.succedent
          val p_ant2 = subst(iter).asInstanceOf[HOLFormula] +: rest.antecedent
          val p_suc2 = rest.succedent
          val premise1 = FSequent(p_ant1, p_suc1)
          val premise2 = FSequent(p_ant2, p_suc2)
          prove(premise1, strategy) match {
            case Some(proof1) => prove(premise2, strategy) match {
              case Some(proof2) =>
                val proof3 = OrLeftRule(proof1, proof2, BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[HOLFormula])
                val or = Or(BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula])
                val proof4 = OrLeftEquivalenceRule1(proof3, or, BigOr(i, iter, from, to))
                val proof5 = addContractions(proof4, seq)
                Some(proof5)
              case None => None
            }
            case None => None
          }
        } // end of BigOr

      case _ => throw new IllegalArgumentException("Invalid formula in prove: "+action.formula)

    } // end of match formula
  }

  
  private def applyActionSuccedent(action: ProofStrategy.Action, seq: FSequent, strategy: ProofStrategy): Option[LKProof] = {
    val rest = FSequent(seq.antecedent, seq.succedent.diff(action.formula :: Nil))

    action.formula match {

      // Unary Rules

      case Neg(f1) =>
        // If the auxiliary formulas already exists, no need to apply the rule
        if (SolveUtils.checkDuplicate(f1.asInstanceOf[HOLFormula] :: Nil, Nil, seq)) {
          prove(rest, strategy).map(WeakeningRightRule(_, action.formula))
        } else {
          val p_ant = f1.asInstanceOf[HOLFormula] +: rest.antecedent
          val p_suc = rest.succedent
          val premise = FSequent(p_ant, p_suc)
          prove(premise, strategy) match {
            case Some(p) =>
              val p1 = NegRightRule(p, f1.asInstanceOf[HOLFormula])
              Some(p1)
            case None => None
          }
        }

      // Binary Rules

      case Imp(f1, f2) =>
        // If the auxiliary formulas already exists, no need to apply the rule
        if (SolveUtils.checkDuplicate(f1.asInstanceOf[HOLFormula] :: Nil, f2.asInstanceOf[HOLFormula] :: Nil, seq)) {
          prove(rest, strategy).map(WeakeningRightRule(_, action.formula))
        } else {
          val p_ant = f1.asInstanceOf[HOLFormula] +: rest.antecedent
          val p_suc = f2.asInstanceOf[HOLFormula] +: rest.succedent
          val premise = FSequent(p_ant, p_suc)
          prove(premise, strategy) match {
            case Some(p) =>
              val p1 = ImpRightRule(p, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
              Some(p1)
            case None => None
          }
        }

      case Or(f1, f2) =>
        // If the auxiliary formulas already exists, no need to apply the rule
        if (SolveUtils.checkDuplicate(Nil, f1.asInstanceOf[HOLFormula] :: f2.asInstanceOf[HOLFormula] :: Nil, seq)) {
          prove(rest, strategy).map(WeakeningRightRule(_, action.formula))
        } else if (SolveUtils.checkDuplicate(Nil, f2.asInstanceOf[HOLFormula] :: Nil, seq)) {
          val up_ant = rest.antecedent
          val up_suc = f1.asInstanceOf[HOLFormula] +: rest.succedent
          val upremise = FSequent(up_ant, up_suc)
          prove(upremise, strategy) match {
            case Some(proof) =>
              val proof_or1 = OrRight1Rule(proof, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
              Some(proof_or1)
            case None => None
          }
        }
        else if (SolveUtils.checkDuplicate(Nil, f1.asInstanceOf[HOLFormula] :: Nil, seq)) {
          val up_ant = rest.antecedent
          val up_suc = f2.asInstanceOf[HOLFormula] +: rest.succedent
          val upremise = FSequent(up_ant, up_suc)
          prove(upremise, strategy) match {
            case Some(proof) =>
              val proof_or2 = OrRight2Rule(proof, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
              Some(proof_or2)
            case None => None
          }
        }
        else {
          // For this case, contract the formula and choose the first and then the second conjunct
          val up_ant = rest.antecedent
          val up_suc = f1.asInstanceOf[HOLFormula] +: f2.asInstanceOf[HOLFormula] +: rest.succedent
          val upremise = FSequent(up_ant, up_suc)
          prove(upremise, strategy) match {
            case Some(proof) =>
              val proof_or2 = OrRight2Rule(proof, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
              val proof_or1 = OrRight1Rule(proof_or2, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
              val proof_contr = ContractionRightRule(proof_or1, action.formula)
              Some(proof_contr)
            case None => None
          }
        }

      case And(f1, f2) =>
        // If the auxiliary formulas already exists, no need to apply the rule
        if (SolveUtils.checkDuplicate(Nil, f1.asInstanceOf[HOLFormula] :: Nil, seq) || SolveUtils.checkDuplicate(Nil, f2.asInstanceOf[HOLFormula] :: Nil, seq)) {
          prove(rest, strategy).map(WeakeningRightRule(_, action.formula))
        } else {
          val p_ant1 = rest.antecedent
          val p_suc1 = f1.asInstanceOf[HOLFormula] +: rest.succedent
          val p_ant2 = rest.antecedent
          val p_suc2 = f2.asInstanceOf[HOLFormula] +: rest.succedent
          val premise1 = FSequent(p_ant1, p_suc1)
          val premise2 = FSequent(p_ant2, p_suc2)
          prove(premise2, strategy) match {
            case Some(p2) => prove(premise1, strategy) match {
              case Some(p1) =>
                val p = AndRightRule(p1, p2, f1.asInstanceOf[HOLFormula], f2.asInstanceOf[HOLFormula])
                val p_contr = addContractions(p, seq)
                Some(p_contr)
              case None => None
            }
            case None => None
          }
        }


      // Schematic Rules

      case BigOr(i, iter, from, to) =>
        val i = IntVar(new VariableStringSymbol("i"))
        if (from == to) {
          val new_map = Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          val p_ant = subst(iter).asInstanceOf[SchemaFormula] +: rest.antecedent
          val p_suc = rest.succedent
          val premise = FSequent(p_ant, p_suc)
          prove(premise, strategy) match {
            case Some(proof) =>
              val proof1 = OrRightEquivalenceRule3(proof, subst(iter).asInstanceOf[SchemaFormula], action.formula.asInstanceOf[SchemaFormula])
              Some(proof1)
            case None => None
          }
        }
        else {
          val new_map = Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          val p_ant = rest.antecedent
          val p_suc = BigOr(i, iter, from, Pred(to)) +: subst(iter).asInstanceOf[HOLFormula] +: rest.succedent
          val premise = FSequent(p_ant, p_suc)
          prove(premise, strategy) match {
            case Some(proof) =>
              val proof1 = OrRightRule(proof, BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[HOLFormula])
              val or = Or(BigOr(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula])
              val proof2 = OrRightEquivalenceRule1(proof1, or, BigOr(i, iter, from, to))
              Some(proof2)
            case None => None
          }
        }

      case BigAnd(i, iter, from, to) =>
        val i = IntVar(new VariableStringSymbol("i"))
        if (from == to) {
          val new_map = Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          val p_ant = rest.antecedent
          val p_suc = subst(iter).asInstanceOf[SchemaFormula] +: rest.succedent
          val premise = FSequent(p_ant, p_suc)
          prove(premise, strategy) match {
            case Some(proof) =>
              val proof1 = AndRightEquivalenceRule3(proof, subst(iter).asInstanceOf[SchemaFormula], action.formula.asInstanceOf[SchemaFormula])
              Some(proof1)
            case None => None
          }
        }
        else {
          val new_map = Map[Var, HOLExpression]() + Pair(i, to)
          val subst = new SchemaSubstitution1[HOLExpression](new_map)
          val p_ant1 = rest.antecedent
          val p_suc1 = BigAnd(i, iter, from, Pred(to)) +: rest.succedent
          val p_ant2 = rest.antecedent
          val p_suc2 = subst(iter).asInstanceOf[HOLFormula] +: rest.succedent
          val premise1 = FSequent(p_ant1, p_suc1)
          val premise2 = FSequent(p_ant2, p_suc2)
          prove(premise1, strategy) match {
            case Some(proof1) => prove(premise2, strategy) match {
              case Some(proof2) =>
                val proof3 = AndRightRule(proof1, proof2, BigAnd(i, iter, from, Pred(to)), subst(iter).asInstanceOf[HOLFormula])
                val and = And(BigAnd(i, iter, from, Pred(to)), subst(iter).asInstanceOf[SchemaFormula])
                val proof4 = AndRightEquivalenceRule1(proof3, and, BigAnd(i, iter, from, to))
                val proof5 = addContractions(proof4, seq)
                Some(proof5)
              case None => None
            }
            case None => None
          }
        }


      case _ => throw new IllegalArgumentException("Invalid formula in prove: " + action.formula)

    } // end of match formula
  }
}

/**
 * Strategy to tell prove procedure which rules to apply
 * Basic strategies are PropositionalStrategy and ExpansionTreeStrategy
 */
abstract class ProofStrategy {
  def calcNextStep(seq: FSequent): ProofStrategy.Action
}
object ProofStrategy {
  object FormulaLocation extends Enumeration { val Succedent, Antecedent = Value }
  class Action(val formula: HOLFormula, val loc: FormulaLocation.Value) {}
}

class PropositionalProofStrategy extends ProofStrategy {
  val FormulaLocation = ProofStrategy.FormulaLocation

  override def calcNextStep(seq: FSequent): ProofStrategy.Action = {

    if (SolveUtils.isAxiom(seq)) {
      throw new RuntimeException("Prove strategy called on axiom: " + seq)
    } else if (SolveUtils.findNonschematicAxiom(seq).isDefined) {
      throw new RuntimeException("Prove strategy called on axiom: " + seq)
    } else {

      // rule preference:
      // NOTE: getOrElse uses call by name, i.e. functions below are only evaluated if really needed
      findUnaryLeft(seq).getOrElse(
        findUnaryRight(seq).getOrElse(
          findBinaryLeft(seq).getOrElse(
            findBinaryRight(seq).getOrElse(
              throw new RuntimeException("PropositionalProofStrategy is unable to find a rule to apply on: "+seq)
            )
          )
        )
      )
    }
  }

  // Tries to find a formula on the left or on the right such that its
  // introduction rule is unary.
  def findUnaryLeft(seq: FSequent) : Option[ProofStrategy.Action] =
    seq.antecedent.find(f => f match {
      case Neg(_) | And(_,_) | BigAnd(_,_,_,_) => true
      case _ => false
    }).map(new ProofStrategy.Action(_, FormulaLocation.Antecedent))
  def findUnaryRight(seq: FSequent) : Option[ProofStrategy.Action] =
    seq.succedent.find(f => f match {
      case Neg(_) | Imp(_,_) | Or(_,_) | BigOr(_,_,_,_) => true
      case _ => false
    }).map(new ProofStrategy.Action(_, FormulaLocation.Succedent))

  // Tries to find a formula on the left or on the right such that its
  // introduction rule is binary.
  def findBinaryLeft(seq: FSequent) : Option[ProofStrategy.Action] =
    seq.antecedent.find(f => f match {
      case Imp(_,_) | Or(_,_) | BigOr(_,_,_,_) => true
      case _ => false
    }).map(new ProofStrategy.Action(_, FormulaLocation.Antecedent))
  def findBinaryRight(seq: FSequent) : Option[ProofStrategy.Action] =
    seq.succedent.find(f => f match {
      case And(_,_) | BigAnd(_,_,_,_) => true
      case _ => false
    }).map(new ProofStrategy.Action(_, FormulaLocation.Succedent))


}

class ExpansionTreeProofStrategy extends PropositionalProofStrategy {
  override def calcNextStep(seq: FSequent): ProofStrategy.Action = {
    new ExpansionTreeProofStrategy.ExpansionTreeAction(BottomC, ProofStrategy.FormulaLocation.Antecedent, None, Nil)
  }
}
object ExpansionTreeProofStrategy {
  class ExpansionTreeAction(override val formula: HOLFormula, override val loc: ProofStrategy.FormulaLocation.Value, val et: Option[ExpansionTree], val subStrategies: Seq[ProofStrategy])
    extends ProofStrategy.Action(formula, loc) {}
}


private object SolveUtils extends at.logic.utils.logging.Logger {
    // Checks if the sequent is of the form A, \Gamma |- A, \Delta
  def isAxiom(seq: FSequent): Boolean =
    seq.antecedent.exists(f =>
      seq.succedent.exists(f2 =>
        f == f2 && f.isAtom
      )
    )

  def findNonschematicAxiom(seq: FSequent) : Option[(HOLFormula,HOLFormula)] = {
    val axs = for (f  <- seq.antecedent.toList;
         g <- seq.succedent.toList;
         if f == g && isNotSchematic(f)
      ) yield { (f,g) }

    axs match {
      case Nil => None
      case (f,g)::_ => Some((f,g))
    }
  }

  private def isNotSchematic(f:HOLFormula) : Boolean = f match {
    case Atom(_,_) => true
    case Neg(l) => isNotSchematic(l.asInstanceOf[HOLFormula])
    case And(l,r) => isNotSchematic(l.asInstanceOf[HOLFormula]) && isNotSchematic(r.asInstanceOf[HOLFormula])
    case Or(l,r) => isNotSchematic(l.asInstanceOf[HOLFormula]) && isNotSchematic(r.asInstanceOf[HOLFormula])
    case Imp(l,r) => isNotSchematic(l.asInstanceOf[HOLFormula]) && isNotSchematic(r.asInstanceOf[HOLFormula])
    case AllVar(_,l)  => isNotSchematic(l.asInstanceOf[HOLFormula])
    case ExVar(_,l)  => isNotSchematic(l.asInstanceOf[HOLFormula])
    case BigAnd(_,_,_,_) => false
    case BigOr(_,_,_,_) => false
    case _ => warn("WARNING: Unexpected operator in test for schematic formula "+f); false
  }


  def getAxiomfromSeq(seq: FSequent) : (HOLFormula, FSequent) = {
    if (isAxiom(seq)) {
      seq.antecedent.foreach(f => if (seq.succedent.contains(f)){
        return (f, removeFfromSeqAnt(removeFfromSeqSucc(seq, f), f))
      })
      throw new Exception("\nError in if-autoprop.getAxiomfromSeq !\n")
    }
    else throw new Exception("\nError in else-autoprop.getAxiomfromSeq !\n")
  }

  def removeFfromSeqAnt(seq: FSequent, f : HOLFormula) : FSequent = {
    FSequent(seq.antecedent.filter(x => x != f) , seq.succedent)
  }

  def removeFfromSeqSucc(seq: FSequent, f : HOLFormula) : FSequent = {
    FSequent(seq.antecedent, seq.succedent.filter(x => x != f))
  }

  def removeFfromSeqAnt(seq: FSequent, flist : List[HOLFormula]) : FSequent = {
    FSequent(seq.antecedent.filter(x => !flist.contains(x)) , seq.succedent)
  }

  def removeFfromSeqSucc(seq: FSequent, flist : List[HOLFormula]) : FSequent = {
    FSequent(seq.antecedent, seq.succedent.filter(x => !flist.contains(x)))
  }

  // Checks if the atoms occurring in seq are all different (if so, the sequent
  // is not provable.
  def noCommonAtoms(seq: FSequent) : Boolean = {
    val atoms = getAtoms(seq)
    atoms.size == atoms.toSet.size
  }
    // TODO: move this to sequent!!!!!
  private def getAtoms(seq: FSequent) : List[HOLFormula] = {
    val all = seq.antecedent ++ seq.succedent
    all.foldLeft(List[HOLFormula]()) { case (acc, f) => getAtoms(f) ++ acc }
  }

  // TODO: move this to hol!!!!!!
  private def getAtoms(f: HOLFormula) : List[HOLFormula] = f match {
    case Atom(_,_) => List(f)
    case Neg(f) => getAtoms(f.asInstanceOf[HOLFormula])
    case And(f1,f2) => getAtoms(f1.asInstanceOf[HOLFormula]) ++ getAtoms(f2.asInstanceOf[HOLFormula])
    case Or(f1,f2) => getAtoms(f1.asInstanceOf[HOLFormula]) ++ getAtoms(f2.asInstanceOf[HOLFormula])
    case Imp(f1,f2) => getAtoms(f1.asInstanceOf[HOLFormula]) ++ getAtoms(f2.asInstanceOf[HOLFormula])
    case ExVar(v,f) => getAtoms(f)
    case AllVar(v,f) => getAtoms(f)
  }

  // Checks if seq contains the formulas of lft in the antecedent and the formulas of rght on the succedent
  def checkDuplicate(lft: List[HOLFormula], rght: List[HOLFormula], seq: FSequent) : Boolean = {
    lft.forall(f => seq.antecedent.contains(f)) && rght.forall(f => seq.succedent.contains(f))
  }


}
