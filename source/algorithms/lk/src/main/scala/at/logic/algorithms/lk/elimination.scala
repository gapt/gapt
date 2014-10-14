package at.logic.algorithms.lk

import at.logic.calculi.lk.base._
import at.logic.calculi.lk._
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.language.hol._
import at.logic.language.schema.{And => AndS, Or => OrS, SchemaFormula}
import at.logic.calculi.slk._

/**
 * Removes the redundant weakenings and contractions.
 * Linear algorithm. Traverses the proof top down, keeping track of the
 * weakened formulas. Checks if the auxiliary formulas of each rule are weakened
 * or not and treats it appropriately.
 */
object CleanStructuralRules {

  def apply(p: LKProof) : LKProof = {
    cleanStructuralRules(p, {
      (proof, ws) => addWeakenings(proof, p.root.toFSequent) 
    })
  }

  // Note: using a pair instead of a sequent because sequents are composed of 
  // formula occurrences and not formulas.
  private def cleanStructuralRules(pr: LKProof, fun: ((LKProof, (List[HOLFormula], List[HOLFormula])) => LKProof)) : LKProof = pr match {
    // Base case: axiom
    case Axiom(s) => fun (pr, (Nil, Nil))

    // Structural rules:
    
    case WeakeningLeftRule(p, _, m) => 
      cleanStructuralRules(p, { (proof, ws) =>
	fun (proof, (ws._1 :+ m.formula, ws._2))
      })
    
    case WeakeningRightRule(p, _, m) =>
      cleanStructuralRules(p, { (proof, ws) =>
	fun (proof, (ws._1, ws._2 :+ m.formula))
      })

    case ContractionLeftRule(p, _, a1, a2, m) =>
      cleanStructuralRules(p, { (proof, ws) =>
	ws._1.count(f => f == a1.formula) match {
	  case n if n >= 2 => fun (proof, (ws._1.diff(List(a1.formula, a2.formula)) :+ m.formula, ws._2)) 
	  case n if n == 1 => fun (proof, (ws._1.diff(List(a1.formula)), ws._2))
	  case n if n == 0 => fun (ContractionLeftRule(proof, a1.formula), ws)
	}
      })

    case ContractionRightRule(p, _, a1, a2, m) =>
      cleanStructuralRules(p, { (proof, ws) =>
	ws._2.count(f => f == a1.formula) match {
	  case n if n >= 2 => fun (proof, (ws._1, ws._2.diff(List(a1.formula, a2.formula)) :+ m.formula)) 
	  case n if n == 1 => fun (proof, (ws._1, ws._2.diff(List(a1.formula))))
	  case n if n == 0 => fun (ContractionRightRule(proof, a1.formula), ws)
	}
      })

    case CutRule(p1, p2, _, a1, a2) =>
      cleanStructuralRules(p1, { (proof1, wsl) =>
	cleanStructuralRules(p2, { (proof2, wsr) =>
          (wsl._2.contains(a1.formula), wsr._1.contains(a2.formula)) match {
            case (true, true) => 
              val ant2 = proof2.root.antecedent.map(_.formula)
              val suc2 = proof2.root.succedent.map(_.formula)
              val ws_1 = wsl._1 ++ wsr._1.diff(List(a2.formula)) ++ ant2
              val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2 ++ suc2
              fun (proof1, (ws_1, ws_2)) // The choice for proof1 is arbitrary
            case (true, false) =>
              val ws_1 = wsl._1 ++ wsr._2
              val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
              val p = WeakeningRightRule(proof1, a1.formula)
              fun (CutRule(p, proof2, a1.formula), (ws_1, ws_2))
            case (false, true) =>
              val ws_1 = wsl._1 ++ wsr._1.diff(List(a2.formula))
              val ws_2 = wsl._2 ++ wsr._2
              val p = WeakeningLeftRule(proof2, a2.formula)
              fun (CutRule(proof1, p, a1.formula), (ws_1, ws_2))
            case (false, false) =>
              val ws_1 = wsl._1 ++ wsr._1
              val ws_2 = wsl._2 ++ wsr._2
              fun (CutRule(proof1, proof2, a1.formula), (ws_1, ws_2))
          }
	})
      })

    // Unary rules, one aux formula:

    case NegLeftRule(p, _, a, m) =>
      cleanStructuralRules(p, { (proof, ws) =>
	ws._2.contains(a.formula) match {
	  case true => fun (proof, (ws._1 :+ m.formula, ws._2.diff(List(a.formula))))
	  case false => fun (NegLeftRule(proof, a.formula), ws)
	}
      })
  
    case NegRightRule(p, _, a, m) =>
      cleanStructuralRules(p, { (proof, ws) =>
	ws._1.contains(a.formula) match {
	  case true => fun (proof, (ws._1.diff(List(a.formula)), ws._2 :+ m.formula))
	  case false => fun (NegRightRule(proof, a.formula), ws)
	}
      })

    case AndLeft1Rule(p, _, a, m) =>
      cleanStructuralRules(p, { (proof, ws) =>
	ws._1.contains(a.formula) match {
	  case true => fun (proof, (ws._1.diff(List(a.formula)) :+ m.formula, ws._2))
	  case false => 
	    val And(_, a2) = m.formula
	    fun (AndLeft1Rule(proof, a.formula, a2), ws)
	}
      })

    case AndLeft2Rule(p, _, a, m) =>
      cleanStructuralRules(p, { (proof, ws) =>
	ws._1.contains(a.formula) match {
	  case true => fun (proof, (ws._1.diff(List(a.formula)) :+ m.formula, ws._2))
	  case false => 
	    val And(a1, _) = m.formula
	    fun (AndLeft2Rule(proof, a1, a.formula), ws)
	}
      })
    
    case OrRight1Rule(p, _, a, m) =>
      cleanStructuralRules(p, { (proof, ws) =>
	ws._2.contains(a.formula) match {
	  case true => fun (proof, (ws._1, ws._2.diff(List(a.formula)) :+ m.formula))
	  case false => 
	    val Or(_, a2) = m.formula
	    fun (OrRight1Rule(proof, a.formula, a2), ws)
	}
      })
      
    case OrRight2Rule(p, _, a, m) =>
      cleanStructuralRules(p, { (proof, ws) =>
	ws._2.contains(a.formula) match {
	  case true => fun (proof, (ws._1, ws._2.diff(List(a.formula)) :+ m.formula))
	  case false => 
	    val Or(a1, _) = m.formula
	    fun (OrRight2Rule(proof, a1, a.formula), ws)
	}
      })
 
    case ForallLeftRule(p, _, a, m, t) =>
      cleanStructuralRules(p, { (proof, ws) =>
	ws._1.contains(a.formula) match {
	  case true => fun (proof, (ws._1.diff(List(a.formula)) :+ m.formula, ws._2))
	  case false => fun (ForallLeftRule(proof, a.formula, m.formula, t), ws)
	}
      })

    case ForallRightRule(p, _, a, m, t) => 
      cleanStructuralRules(p, { (proof, ws) =>
	ws._2.contains(a.formula) match {
	  case true => fun (proof, (ws._1, ws._2.diff(List(a.formula)) :+ m.formula))
	  case false => fun (ForallRightRule(proof, a.formula, m.formula, t), ws)
	}
      })

    case ExistsLeftRule(p, _, a, m, t) => 
      cleanStructuralRules(p, { (proof, ws) =>
	ws._1.contains(a.formula) match {
	  case true => fun (proof, (ws._1.diff(List(a.formula)) :+ m.formula, ws._2))
	  case false => fun (ExistsLeftRule(proof, a.formula, m.formula, t), ws)
	}
      })

    case ExistsRightRule(p, _, a, m, t) => 
      cleanStructuralRules(p, { (proof, ws) =>
	ws._2.contains(a.formula) match {
	  case true => fun (proof, (ws._1, ws._2.diff(List(a.formula)) :+ m.formula))
	  case false => fun (ExistsRightRule(proof, a.formula, m.formula, t), ws)
	}
      })

    // Schema rules (all unary with one aux formula):
    case AndLeftEquivalenceRule1(p, _, a, m) => 
      cleanStructuralRules(p, { (proof, ws) =>
	ws._1.contains(a.formula) match {
	  case true => fun (proof, (ws._1.diff(List(a.formula)) :+ m.formula, ws._2))
	  case false => fun (AndLeftEquivalenceRule1(proof, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula]), ws)
	}
      })

    case AndRightEquivalenceRule1(p, _, a, m) => 
      cleanStructuralRules(p, { (proof, ws) =>
	ws._2.contains(a.formula) match {
	  case true => fun (proof, (ws._1, ws._2.diff(List(a.formula)) :+ m.formula))
	  case false => fun (AndRightEquivalenceRule1(proof, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula]), ws)
	}
      })
    
    case OrLeftEquivalenceRule1(p, _, a, m) => 
      cleanStructuralRules(p, { (proof, ws) =>
	ws._1.contains(a.formula) match {
	  case true => fun (proof, (ws._1.diff(List(a.formula)) :+ m.formula, ws._2))
	  case false => fun (OrLeftEquivalenceRule1(proof, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula]), ws)
	}
      })
    
    case OrRightEquivalenceRule1(p, _, a, m) => 
      cleanStructuralRules(p, { (proof, ws) =>
	ws._2.contains(a.formula) match {
	  case true => fun (proof, (ws._1, ws._2.diff(List(a.formula)) :+ m.formula))
	  case false => fun (OrRightEquivalenceRule1(proof, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula]), ws)
	}
      })
    
    case AndLeftEquivalenceRule3(p, _, a, m) => 
      cleanStructuralRules(p, { (proof, ws) =>
	ws._1.contains(a.formula) match {
	  case true => fun (proof, (ws._1.diff(List(a.formula)) :+ m.formula, ws._2))
	  case false => fun (AndLeftEquivalenceRule3(proof, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula]), ws)
	}
      })
    
    case AndRightEquivalenceRule3(p, _, a, m) => 
      cleanStructuralRules(p, { (proof, ws) =>
	ws._2.contains(a.formula) match {
	  case true => fun (proof, (ws._1, ws._2.diff(List(a.formula)) :+ m.formula))
	  case false => fun (AndRightEquivalenceRule3(proof, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula]), ws)
	}
      })
    
    case OrLeftEquivalenceRule3(p, _, a, m) =>
      cleanStructuralRules(p, { (proof, ws) =>
	ws._1.contains(a.formula) match {
	  case true => fun (proof, (ws._1.diff(List(a.formula)) :+ m.formula, ws._2))
	  case false => fun (OrLeftEquivalenceRule3(proof, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula]), ws)
	}
      })
    
    case OrRightEquivalenceRule3(p, _, a, m) => 
      cleanStructuralRules(p, { (proof, ws) =>
	ws._2.contains(a.formula) match {
	  case true => fun (proof, (ws._1, ws._2.diff(List(a.formula)) :+ m.formula))
	  case false => fun (OrRightEquivalenceRule3(proof, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula]), ws)
	}
      })

    // Definition rules (all unary with one aux formula):
    case DefinitionLeftRule(p, _, a, m) =>
      cleanStructuralRules(p, { (proof, ws) =>
	ws._1.contains(a.formula) match {
	  case true => fun (proof, (ws._1.diff(List(a.formula)) :+ m.formula, ws._2))
	  case false => fun (DefinitionLeftRule(proof, a.formula, m.formula), ws)
	}
      })

    case DefinitionRightRule(p, _, a, m) =>
      cleanStructuralRules(p, { (proof, ws) =>
	ws._2.contains(a.formula) match {
	  case true => fun (proof, (ws._1, ws._2.diff(List(a.formula)) :+ m.formula))
	  case false => fun (DefinitionRightRule(proof, a.formula, m.formula), ws)
	}
      })

    // Unary rules, two aux formulas:

    case ImpRightRule(p, _, a1, a2, m) =>
      cleanStructuralRules(p, { (proof, ws) =>
        (ws._1.contains(a1.formula), ws._2.contains(a2.formula)) match {
          case (true, true) => 
            val ws_1 = ws._1.diff(List(a1.formula))
            val ws_2 = ws._2.diff(List(a2.formula)) :+ m.formula
            fun (proof, (ws_1, ws_2)) 
          case (true, false) => 
            val p1 = WeakeningLeftRule(proof, a1.formula)
            val p2 = ImpRightRule(p1, a1.formula, a2.formula)
            fun (p2, (ws._1.diff(List(a1.formula)), ws._2))
          case (false, true) => 
            val p1 = WeakeningRightRule(proof, a2.formula)
            val p2 = ImpRightRule(p1, a1.formula, a2.formula)
            fun (p2, (ws._1, ws._2.diff(List(a2.formula))))
	  case (false, false) => fun (ImpRightRule(proof, a1.formula, a2.formula), ws)
        }
      })

    // Binary rules:

    case OrLeftRule(p1, p2, _, a1, a2, m) =>
      cleanStructuralRules(p1, { (proof1, wsl) =>
	cleanStructuralRules(p2, { (proof2, wsr) =>
          (wsl._1.contains(a1.formula), wsr._1.contains(a2.formula)) match {
            case (true, true) => 
              val ant2 = proof2.root.antecedent.map(_.formula)
              val suc2 = proof2.root.succedent.map(_.formula)
              val ws_1 = ((wsl._1.diff(List(a1.formula)) ++ wsr._1.diff(List(a2.formula))) :+ m.formula) ++ ant2
              val ws_2 = wsl._2 ++ wsr._2 ++ suc2
              fun (proof1, (ws_1, ws_2)) // The choice for proof1 is arbitrary
            case (true, false) =>
              val ws_1 = wsl._1.diff(List(a1.formula)) ++ wsr._1
              val ws_2 = wsl._2 ++ wsr._2
              val p = WeakeningLeftRule(proof1, a1.formula)
              fun (OrLeftRule(p, proof2, a1.formula, a2.formula), (ws_1, ws_2))
            case (false, true) =>
              val ws_1 = wsl._1 ++ wsr._1.diff(List(a2.formula))
              val ws_2 = wsl._2 ++ wsr._2
              val p = WeakeningLeftRule(proof2, a2.formula)
              fun (OrLeftRule(proof1, p, a1.formula, a2.formula), (ws_1, ws_2))
            case (false, false) =>
              val ws_1 = wsl._1 ++ wsr._1
              val ws_2 = wsl._2 ++ wsr._2
              fun (OrLeftRule(proof1, proof2, a1.formula, a2.formula), (ws_1, ws_2))
          }
	})
      })

    case AndRightRule(p1, p2, _, a1, a2, m) =>
      cleanStructuralRules(p1, { (proof1, wsl) =>
	cleanStructuralRules(p2, { (proof2, wsr) =>
          (wsl._2.contains(a1.formula), wsr._2.contains(a2.formula)) match {
            case (true, true) => 
              val ant2 = proof2.root.antecedent.map(_.formula)
              val suc2 = proof2.root.succedent.map(_.formula)
              val ws_1 = wsl._1 ++ wsr._1 ++ ant2
              val ws_2 = ((wsl._2.diff(List(a1.formula)) ++ wsr._2.diff(List(a2.formula))) :+ m.formula) ++ suc2
              fun (proof1, (ws_1, ws_2)) // The choice for proof1 is arbitrary
            case (true, false) =>
              val ws_1 = wsl._1 ++ wsr._1
              val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
              val p = WeakeningRightRule(proof1, a1.formula)
              fun (AndRightRule(p, proof2, a1.formula, a2.formula), (ws_1, ws_2))
            case (false, true) =>
              val ws_1 = wsl._1 ++ wsr._1
              val ws_2 = wsl._2 ++ wsr._2.diff(List(a2.formula))
              val p = WeakeningRightRule(proof2, a2.formula)
              fun (AndRightRule(proof1, p, a1.formula, a2.formula), (ws_1, ws_2))
            case (false, false) =>
              val ws_1 = wsl._1 ++ wsr._1
              val ws_2 = wsl._2 ++ wsr._2
              fun (AndRightRule(proof1, proof2, a1.formula, a2.formula), (ws_1, ws_2))
          }
	})
      })

    case ImpLeftRule(p1, p2, _, a1, a2, m) =>
      cleanStructuralRules(p1, { (proof1, wsl) =>
	cleanStructuralRules(p2, { (proof2, wsr) =>
          (wsl._2.contains(a1.formula), wsr._1.contains(a2.formula)) match {
            case (true, true) => 
              val ant2 = proof2.root.antecedent.map(_.formula)
              val suc2 = proof2.root.succedent.map(_.formula)
              val ws_1 = ((wsl._1 ++ wsr._1.diff(List(a2.formula))) :+ m.formula) ++ ant2
              val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2 ++ suc2
              fun (proof1, (ws_1, ws_2)) // The choice for proof1 is arbitrary
            case (true, false) =>
              val ws_1 = wsl._1 ++ wsr._1
              val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
              val p = WeakeningRightRule(proof1, a1.formula)
              fun (ImpLeftRule(p, proof2, a1.formula, a2.formula), (ws_1, ws_2))
            case (false, true) =>
              val ws_1 = wsl._1 ++ wsr._1.diff(List(a2.formula))
              val ws_2 = wsl._2 ++ wsr._2
              val p = WeakeningLeftRule(proof2, a2.formula)
              fun (ImpLeftRule(proof1, p, a1.formula, a2.formula), (ws_1, ws_2))
            case (false, false) =>
              val ws_1 = wsl._1 ++ wsr._1
              val ws_2 = wsl._2 ++ wsr._2
              fun (ImpLeftRule(proof1, proof2, a1.formula, a2.formula), (ws_1, ws_2))
          }
	})
      })
   
    // Equation rules (all binary):
    case EquationLeft1Rule(p1, p2, _, a1, a2, m) =>
      cleanStructuralRules(p1, { (proof1, wsl) =>
	cleanStructuralRules(p2, { (proof2, wsr) =>
          (wsl._2.contains(a1.formula), wsr._1.contains(a2.formula)) match {
            case (true, true) => 
              val ant2 = proof2.root.antecedent.map(_.formula)
              val suc2 = proof2.root.succedent.map(_.formula)
              val ws_1 = ((wsl._1 ++ wsr._1.diff(List(a2.formula))) :+ m.formula) ++ ant2
              val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2 ++ suc2
              fun (proof1, (ws_1, ws_2)) // The choice for proof1 is arbitrary
            case (true, false) =>
              val ws_1 = wsl._1 ++ wsr._1
              val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
              val p = WeakeningRightRule(proof1, a1.formula)
              fun (EquationLeft1Rule(p, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2))
            case (false, true) =>
              val ws_1 = wsl._1 ++ wsr._1.diff(List(a2.formula))
              val ws_2 = wsl._2 ++ wsr._2
              val p = WeakeningLeftRule(proof2, a2.formula)
              fun (EquationLeft1Rule(proof1, p, a1.formula, a2.formula, m.formula), (ws_1, ws_2))
            case (false, false) =>
              val ws_1 = wsl._1 ++ wsr._1
              val ws_2 = wsl._2 ++ wsr._2
              fun (EquationLeft1Rule(proof1, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2))
          }
	})
      })

    case EquationLeft2Rule(p1, p2, _, a1, a2, m) =>
      cleanStructuralRules(p1, { (proof1, wsl) =>
	cleanStructuralRules(p2, { (proof2, wsr) =>
          (wsl._2.contains(a1.formula), wsr._1.contains(a2.formula)) match {
            case (true, true) => 
              val ant2 = proof2.root.antecedent.map(_.formula)
              val suc2 = proof2.root.succedent.map(_.formula)
              val ws_1 = ((wsl._1 ++ wsr._1.diff(List(a2.formula))) :+ m.formula) ++ ant2
              val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2 ++ suc2
              fun (proof1, (ws_1, ws_2)) // The choice for proof1 is arbitrary
            case (true, false) =>
              val ws_1 = wsl._1 ++ wsr._1
              val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
              val p = WeakeningRightRule(proof1, a1.formula)
              fun (EquationLeft2Rule(p, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2))
            case (false, true) =>
              val ws_1 = wsl._1 ++ wsr._1.diff(List(a2.formula))
              val ws_2 = wsl._2 ++ wsr._2
              val p = WeakeningLeftRule(proof2, a2.formula)
              fun (EquationLeft2Rule(proof1, p, a1.formula, a2.formula, m.formula), (ws_1, ws_2))
            case (false, false) =>
              val ws_1 = wsl._1 ++ wsr._1
              val ws_2 = wsl._2 ++ wsr._2
              fun (EquationLeft2Rule(proof1, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2))
          }
	})
      })

    case EquationRight1Rule(p1, p2, _, a1, a2, m) =>
      cleanStructuralRules(p1, { (proof1, wsl) =>
	cleanStructuralRules(p2, { (proof2, wsr) =>
          (wsl._2.contains(a1.formula), wsr._2.contains(a2.formula)) match {
            case (true, true) => 
              val ant2 = proof2.root.antecedent.map(_.formula)
              val suc2 = proof2.root.succedent.map(_.formula)
              val ws_1 = wsl._1 ++ wsr._1 ++ ant2
              val ws_2 = ((wsl._2.diff(List(a1.formula)) ++ wsr._2.diff(List(a2.formula))) :+ m.formula) ++ suc2
              fun (proof1, (ws_1, ws_2)) // The choice for proof1 is arbitrary
            case (true, false) =>
              val ws_1 = wsl._1 ++ wsr._1
              val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
              val p = WeakeningRightRule(proof1, a1.formula)
              fun (EquationRight1Rule(p, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2))
            case (false, true) =>
              val ws_1 = wsl._1 ++ wsr._1
              val ws_2 = wsl._2 ++ wsr._2.diff(List(a2.formula))
              val p = WeakeningRightRule(proof2, a2.formula)
              fun (EquationRight1Rule(proof1, p, a1.formula, a2.formula, m.formula), (ws_1, ws_2))
            case (false, false) =>
              val ws_1 = wsl._1 ++ wsr._1
              val ws_2 = wsl._2 ++ wsr._2
              fun (EquationRight1Rule(proof1, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2))
          }
	})
      })

    case EquationRight2Rule(p1, p2, _, a1, a2, m) =>
      cleanStructuralRules(p1, { (proof1, wsl) =>
	cleanStructuralRules(p2, { (proof2, wsr) =>
          (wsl._2.contains(a1.formula), wsr._2.contains(a2.formula)) match {
            case (true, true) => 
              val ant2 = proof2.root.antecedent.map(_.formula)
              val suc2 = proof2.root.succedent.map(_.formula)
              val ws_1 = wsl._1 ++ wsr._1 ++ ant2
              val ws_2 = ((wsl._2.diff(List(a1.formula)) ++ wsr._2.diff(List(a2.formula))) :+ m.formula) ++ suc2
              fun (proof1, (ws_1, ws_2)) // The choice for proof1 is arbitrary
            case (true, false) =>
              val ws_1 = wsl._1 ++ wsr._1
              val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
              val p = WeakeningRightRule(proof1, a1.formula)
              fun (EquationRight2Rule(p, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2))
            case (false, true) =>
              val ws_1 = wsl._1 ++ wsr._1
              val ws_2 = wsl._2 ++ wsr._2.diff(List(a2.formula))
              val p = WeakeningRightRule(proof2, a2.formula)
              fun (EquationRight2Rule(proof1, p, a1.formula, a2.formula, m.formula), (ws_1, ws_2))
            case (false, false) =>
              val ws_1 = wsl._1 ++ wsr._1
              val ws_2 = wsl._2 ++ wsr._2
              fun (EquationRight2Rule(proof1, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2))
          }
	})
      })

    case _ => throw new Exception("ERROR: Unexpected case while cleaning redundant structural rules.")
  }
}
