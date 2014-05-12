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
 * TODO: make it tail-recursive.
 */
object CleanStructuralRules {

  def apply(p: LKProof) : LKProof = {
    val (proof, ws) = cleanStructuralRules(p)
    addWeakenings(proof, p.root.toFSequent)
  }

  // Note: using a pair instead of a sequent because sequents are composed of 
  // formula occurrences and not formulas.
  private def cleanStructuralRules(pr: LKProof) : (LKProof, (List[HOLFormula], List[HOLFormula])) = pr match {
    // Base case: axiom
    case Axiom(s) => ( pr, (Nil, Nil) )

    // Structural rules:
    
    case WeakeningLeftRule(p, _, m) => 
      val (proof, ws) = cleanStructuralRules(p)
      ( proof, (ws._1 :+ m.formula, ws._2) )
    
    case WeakeningRightRule(p, _, m) =>
      val (proof, ws) = cleanStructuralRules(p)
      ( proof, (ws._1, ws._2 :+ m.formula) )

    case ContractionLeftRule(p, _, a1, a2, m) =>
      val (proof, ws) = cleanStructuralRules(p)
      ws._1.count(f => f == a1.formula) match {
        case n if n >= 2 => ( proof, (ws._1.diff(List(a1.formula, a2.formula)) :+ m.formula, ws._2) ) 
        case n if n == 1 => ( proof, (ws._1.diff(List(a1.formula)), ws._2) )
        case n if n == 0 => ( ContractionLeftRule(proof, a1.formula), ws )
      }

    case ContractionRightRule(p, _, a1, a2, m) =>
      val (proof, ws) = cleanStructuralRules(p)
      ws._2.count(f => f == a1.formula) match {
        case n if n >= 2 => ( proof, (ws._1, ws._2.diff(List(a1.formula, a2.formula)) :+ m.formula) ) 
        case n if n == 1 => ( proof, (ws._1, ws._2.diff(List(a1.formula))) )
        case n if n == 0 => ( ContractionRightRule(proof, a1.formula), ws )
      }
 
    case CutRule(p1, p2, _, a1, a2) =>
      val (proof1, wsl) = cleanStructuralRules(p1)
      val (proof2, wsr) = cleanStructuralRules(p2)
      ( wsl._2.contains(a1.formula), wsr._1.contains(a2.formula) ) match {
        case (true, true) => 
          val ant2 = proof2.root.antecedent.map(_.formula)
          val suc2 = proof2.root.succedent.map(_.formula)
          val ws_1 = wsl._1 ++ wsr._1.diff(List(a2.formula)) ++ ant2
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2 ++ suc2
          (proof1, (ws_1, ws_2)) // The choice for proof1 is arbitrary
        case (true, false) =>
          val ws_1 = wsl._1 ++ wsr._2
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
          val p = WeakeningRightRule(proof1, a1.formula)
          ( CutRule(p, proof2, a1.formula), (ws_1, ws_2) )
        case (false, true) =>
          val ws_1 = wsl._1 ++ wsr._1.diff(List(a2.formula))
          val ws_2 = wsl._2 ++ wsr._2
          val p = WeakeningLeftRule(proof2, a2.formula)
          ( CutRule(proof1, p, a1.formula), (ws_1, ws_2) )
        case (false, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2
          ( CutRule(proof1, proof2, a1.formula), (ws_1, ws_2) )
      }

    // Unary rules, one aux formula:

    case NegLeftRule(p, _, a, m) =>
      val (proof, ws) = cleanStructuralRules(p) 
      ws._2.contains(a.formula) match {
        case true => ( proof, (ws._1 :+ m.formula, ws._2.diff(List(a.formula))) )
        case false => ( NegLeftRule(proof, a.formula), ws )
      }
  
    case NegRightRule(p, _, a, m) =>
      val (proof, ws) = cleanStructuralRules(p) 
      ws._1.contains(a.formula) match {
        case true => ( proof, (ws._1.diff(List(a.formula)), ws._2 :+ m.formula) )
        case false => ( NegRightRule(proof, a.formula), ws )
      }

    case AndLeft1Rule(p, _, a, m) =>
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_left(proof, ws, a.formula, m.formula, { (p, a, m) =>
        val a2 = m match {case And(_, r) => r}; AndLeft1Rule(p, a, a2) } )
    
    case AndLeft2Rule(p, _, a, m) =>
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_left(proof, ws, a.formula, m.formula, { (p, a, m) =>
        val a2 = m match {case And(l, _) => l}; AndLeft2Rule(p, a2, a) } )
    
    case OrRight1Rule(p, _, a, m) =>
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_right(proof, ws, a.formula, m.formula, { (p, a, m) =>
        val a2 = m match {case Or(_, r) => r}; OrRight1Rule(p, a, a2) } )
    
    case OrRight2Rule(p, _, a, m) =>
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_right(proof, ws, a.formula, m.formula, { (p, a, m) =>
        val a2 = m match {case Or(l, _) => l}; OrRight2Rule(p, a2, a) } )
 
    case ForallLeftRule(p, _, a, m, t) =>
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_left(proof, ws, a.formula, m.formula, { (p, a, m) => ForallLeftRule(p, a, m, t) } )

    case ForallRightRule(p, _, a, m, t) => 
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_right(proof, ws, a.formula, m.formula, { (p, a, m) => ForallRightRule(p, a, m, t) } )

    case ExistsLeftRule(p, _, a, m, t) => 
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_left(proof, ws, a.formula, m.formula, { (p, a, m) => ExistsLeftRule(p, a, m, t) } )

    case ExistsRightRule(p, _, a, m, t) => 
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_right(proof, ws, a.formula, m.formula, { (p, a, m) => ExistsRightRule(p, a, m, t) } )

    // Schema rules (all unary with one aux formula):
    case AndLeftEquivalenceRule1(p, _, a, m) => 
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_left(proof, ws, a.formula, m.formula, { (p, a, m) => AndLeftEquivalenceRule1(p, a.asInstanceOf[SchemaFormula], m.asInstanceOf[SchemaFormula]) } )

    case AndRightEquivalenceRule1(p, _, a, m) => 
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_right(proof, ws, a.formula, m.formula, { (p, a, m) => AndRightEquivalenceRule1(p, a.asInstanceOf[SchemaFormula], m.asInstanceOf[SchemaFormula]) } )
    
    case OrLeftEquivalenceRule1(p, _, a, m) => 
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_left(proof, ws, a.formula, m.formula, { (p, a, m) => OrLeftEquivalenceRule1(p, a.asInstanceOf[SchemaFormula], m.asInstanceOf[SchemaFormula]) } )
    
    case OrRightEquivalenceRule1(p, _, a, m) => 
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_right(proof, ws, a.formula, m.formula, { (p, a, m) => OrRightEquivalenceRule1(p, a.asInstanceOf[SchemaFormula], m.asInstanceOf[SchemaFormula]) } )
    
    case AndLeftEquivalenceRule3(p, _, a, m) => 
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_left(proof, ws, a.formula, m.formula, { (p, a, m) => AndLeftEquivalenceRule3(p, a.asInstanceOf[SchemaFormula], m.asInstanceOf[SchemaFormula]) } )
    
    case AndRightEquivalenceRule3(p, _, a, m) => 
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_right(proof, ws, a.formula, m.formula, { (p, a, m) => AndRightEquivalenceRule3(p, a.asInstanceOf[SchemaFormula], m.asInstanceOf[SchemaFormula]) } )
    
    case OrLeftEquivalenceRule3(p, _, a, m) =>
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_left(proof, ws, a.formula, m.formula, { (p, a, m) => OrLeftEquivalenceRule3(p, a.asInstanceOf[SchemaFormula], m.asInstanceOf[SchemaFormula]) } )
    
    case OrRightEquivalenceRule3(p, _, a, m) => 
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_right(proof, ws, a.formula, m.formula, { (p, a, m) => OrRightEquivalenceRule3(p, a.asInstanceOf[SchemaFormula], m.asInstanceOf[SchemaFormula]) } )

    // Definition rules (all unary with one aux formula):
    case DefinitionLeftRule(p, _, a, m) =>
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_left(proof, ws, a.formula, m.formula, { (p, a, m) => DefinitionLeftRule(p, a, m) } )

    case DefinitionRightRule(p, _, a, m) =>
      val (proof, ws) = cleanStructuralRules(p)
      handle_unary_one_aux_right(proof, ws, a.formula, m.formula, { (p, a, m) => DefinitionRightRule(p, a, m) } )

    // Unary rules, two aux formulas:

    case ImpRightRule(p, _, a1, a2, m) =>
      val (proof, ws) = cleanStructuralRules(p)
      (ws._1.contains(a1.formula), ws._2.contains(a2.formula)) match {
        case (true, true) => 
          val ws_1 = ws._1.diff(List(a1.formula))
          val ws_2 = ws._2.diff(List(a2.formula)) :+ m.formula
          ( proof, (ws_1, ws_2) ) 
        case (true, false) => 
          val p1 = WeakeningLeftRule(proof, a1.formula)
          val p2 = ImpRightRule(p1, a1.formula, a2.formula)
          ( p2, (ws._1.diff(List(a1.formula)), ws._2) )
        case (false, true) => 
          val p1 = WeakeningRightRule(proof, a2.formula)
          val p2 = ImpRightRule(p1, a1.formula, a2.formula)
          ( p2, (ws._1, ws._2.diff(List(a2.formula))) )
        case (false, false) => ( ImpRightRule(proof, a1.formula, a2.formula), ws )
      }

    // Binary rules:

    case OrLeftRule(p1, p2, _, a1, a2, m) =>
      val (proof1, wsl) = cleanStructuralRules(p1)
      val (proof2, wsr) = cleanStructuralRules(p2)
      (wsl._1.contains(a1.formula), wsr._1.contains(a2.formula)) match {
        case (true, true) => 
          val ant2 = proof2.root.antecedent.map(_.formula)
          val suc2 = proof2.root.succedent.map(_.formula)
          val ws_1 = (( wsl._1.diff(List(a1.formula)) ++ wsr._1.diff(List(a2.formula)) ) :+ m.formula) ++ ant2
          val ws_2 = wsl._2 ++ wsr._2 ++ suc2
          ( proof1, (ws_1, ws_2) ) // The choice for proof1 is arbitrary
        case (true, false) =>
          val ws_1 = wsl._1.diff(List(a1.formula)) ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2
          val p = WeakeningLeftRule(proof1, a1.formula)
          ( OrLeftRule(p, proof2, a1.formula, a2.formula), (ws_1, ws_2) )
        case (false, true) =>
          val ws_1 = wsl._1 ++ wsr._1.diff(List(a2.formula))
          val ws_2 = wsl._2 ++ wsr._2
          val p = WeakeningLeftRule(proof2, a2.formula)
          ( OrLeftRule(proof1, p, a1.formula, a2.formula), (ws_1, ws_2) )
        case (false, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2
          ( OrLeftRule(proof1, proof2, a1.formula, a2.formula), (ws_1, ws_2) )
      }

    case AndRightRule(p1, p2, _, a1, a2, m) =>
      val (proof1, wsl) = cleanStructuralRules(p1)
      val (proof2, wsr) = cleanStructuralRules(p2)
      (wsl._2.contains(a1.formula), wsr._2.contains(a2.formula)) match {
        case (true, true) => 
          val ant2 = proof2.root.antecedent.map(_.formula)
          val suc2 = proof2.root.succedent.map(_.formula)
          val ws_1 = wsl._1 ++ wsr._1 ++ ant2
          val ws_2 = ((wsl._2.diff(List(a1.formula)) ++ wsr._2.diff(List(a2.formula))) :+ m.formula) ++ suc2
          ( proof1, (ws_1, ws_2) ) // The choice for proof1 is arbitrary
        case (true, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
          val p = WeakeningRightRule(proof1, a1.formula)
          ( AndRightRule(p, proof2, a1.formula, a2.formula), (ws_1, ws_2) )
        case (false, true) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2.diff(List(a2.formula))
          val p = WeakeningRightRule(proof2, a2.formula)
          ( AndRightRule(proof1, p, a1.formula, a2.formula), (ws_1, ws_2) )
        case (false, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2
          ( AndRightRule(proof1, proof2, a1.formula, a2.formula), (ws_1, ws_2) )
      }

    case ImpLeftRule(p1, p2, _, a1, a2, m) =>
      val (proof1, wsl) = cleanStructuralRules(p1)
      val (proof2, wsr) = cleanStructuralRules(p2)
      (wsl._2.contains(a1.formula), wsr._1.contains(a2.formula)) match {
        case (true, true) => 
          val ant2 = proof2.root.antecedent.map(_.formula)
          val suc2 = proof2.root.succedent.map(_.formula)
          val ws_1 = ((wsl._1 ++ wsr._1.diff(List(a2.formula))) :+ m.formula) ++ ant2
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2 ++ suc2
          ( proof1, (ws_1, ws_2) ) // The choice for proof1 is arbitrary
        case (true, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
          val p = WeakeningRightRule(proof1, a1.formula)
          ( ImpLeftRule(p, proof2, a1.formula, a2.formula), (ws_1, ws_2) )
        case (false, true) =>
          val ws_1 = wsl._1 ++ wsr._1.diff(List(a2.formula))
          val ws_2 = wsl._2 ++ wsr._2
          val p = WeakeningLeftRule(proof2, a2.formula)
          ( ImpLeftRule(proof1, p, a1.formula, a2.formula), (ws_1, ws_2) )
        case (false, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2
          ( ImpLeftRule(proof1, proof2, a1.formula, a2.formula), (ws_1, ws_2) )
      }
   
    // Equation rules (all binary):
    case EquationLeft1Rule(p1, p2, _, a1, a2, m) =>
      val (proof1, wsl) = cleanStructuralRules(p1)
      val (proof2, wsr) = cleanStructuralRules(p2)
      (wsl._2.contains(a1.formula), wsr._1.contains(a2.formula)) match {
        case (true, true) => 
          val ant2 = proof2.root.antecedent.map(_.formula)
          val suc2 = proof2.root.succedent.map(_.formula)
          val ws_1 = ((wsl._1 ++ wsr._1.diff(List(a2.formula))) :+ m.formula) ++ ant2
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2 ++ suc2
          ( proof1, (ws_1, ws_2) ) // The choice for proof1 is arbitrary
        case (true, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
          val p = WeakeningRightRule(proof1, a1.formula)
          ( EquationLeft1Rule(p, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
        case (false, true) =>
          val ws_1 = wsl._1 ++ wsr._1.diff(List(a2.formula))
          val ws_2 = wsl._2 ++ wsr._2
          val p = WeakeningLeftRule(proof2, a2.formula)
          ( EquationLeft1Rule(proof1, p, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
        case (false, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2
          ( EquationLeft1Rule(proof1, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
      }

    case EquationLeft2Rule(p1, p2, _, a1, a2, m) =>
      val (proof1, wsl) = cleanStructuralRules(p1)
      val (proof2, wsr) = cleanStructuralRules(p2)
      (wsl._2.contains(a1.formula), wsr._1.contains(a2.formula)) match {
        case (true, true) => 
          val ant2 = proof2.root.antecedent.map(_.formula)
          val suc2 = proof2.root.succedent.map(_.formula)
          val ws_1 = ((wsl._1 ++ wsr._1.diff(List(a2.formula))) :+ m.formula) ++ ant2
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2 ++ suc2
          ( proof1, (ws_1, ws_2) ) // The choice for proof1 is arbitrary
        case (true, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
          val p = WeakeningRightRule(proof1, a1.formula)
          ( EquationLeft2Rule(p, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
        case (false, true) =>
          val ws_1 = wsl._1 ++ wsr._1.diff(List(a2.formula))
          val ws_2 = wsl._2 ++ wsr._2
          val p = WeakeningLeftRule(proof2, a2.formula)
          ( EquationLeft2Rule(proof1, p, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
        case (false, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2
          ( EquationLeft2Rule(proof1, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
      }

    case EquationRight1Rule(p1, p2, _, a1, a2, m) =>
      val (proof1, wsl) = cleanStructuralRules(p1)
      val (proof2, wsr) = cleanStructuralRules(p2)
      (wsl._2.contains(a1.formula), wsr._2.contains(a2.formula)) match {
        case (true, true) => 
          val ant2 = proof2.root.antecedent.map(_.formula)
          val suc2 = proof2.root.succedent.map(_.formula)
          val ws_1 = wsl._1 ++ wsr._1 ++ ant2
          val ws_2 = ((wsl._2.diff(List(a1.formula)) ++ wsr._2.diff(List(a2.formula))) :+ m.formula) ++ suc2
          ( proof1, (ws_1, ws_2) ) // The choice for proof1 is arbitrary
        case (true, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
          val p = WeakeningRightRule(proof1, a1.formula)
          ( EquationRight1Rule(p, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
        case (false, true) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2.diff(List(a2.formula))
          val p = WeakeningRightRule(proof2, a2.formula)
          ( EquationRight1Rule(proof1, p, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
        case (false, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2
          ( EquationRight1Rule(proof1, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
      }

    case EquationRight2Rule(p1, p2, _, a1, a2, m) =>
      val (proof1, wsl) = cleanStructuralRules(p1)
      val (proof2, wsr) = cleanStructuralRules(p2)
      (wsl._2.contains(a1.formula), wsr._2.contains(a2.formula)) match {
        case (true, true) => 
          val ant2 = proof2.root.antecedent.map(_.formula)
          val suc2 = proof2.root.succedent.map(_.formula)
          val ws_1 = wsl._1 ++ wsr._1 ++ ant2
          val ws_2 = ((wsl._2.diff(List(a1.formula)) ++ wsr._2.diff(List(a2.formula))) :+ m.formula) ++ suc2
          ( proof1, (ws_1, ws_2) ) // The choice for proof1 is arbitrary
        case (true, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2.diff(List(a1.formula)) ++ wsr._2
          val p = WeakeningRightRule(proof1, a1.formula)
          ( EquationRight2Rule(p, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
        case (false, true) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2.diff(List(a2.formula))
          val p = WeakeningRightRule(proof2, a2.formula)
          ( EquationRight2Rule(proof1, p, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
        case (false, false) =>
          val ws_1 = wsl._1 ++ wsr._1
          val ws_2 = wsl._2 ++ wsr._2
          ( EquationRight2Rule(proof1, proof2, a1.formula, a2.formula, m.formula), (ws_1, ws_2) )
      }

    case _ => throw new Exception("ERROR: Unexpected case while cleaning redundant structural rules.")
  }
  
  
  private def handle_unary_one_aux_left (proof: LKProof, 
                                    ws: (List[HOLFormula], List[HOLFormula]), 
                                    aux: HOLFormula, 
                                    m: HOLFormula,
                                    rule: ((LKProof, HOLFormula, HOLFormula) => LKProof) ) 
  : (LKProof, (List[HOLFormula], List[HOLFormula])) = 
    ws._1.contains(aux) match {
      case true => ( proof, (ws._1.diff(List(aux)) :+ m, ws._2) )
      case false => (rule(proof, aux, m), ws)
    }

  private def handle_unary_one_aux_right (proof: LKProof, 
                                    ws: (List[HOLFormula], List[HOLFormula]), 
                                    aux: HOLFormula, 
                                    m: HOLFormula,
                                    rule: ((LKProof, HOLFormula, HOLFormula) => LKProof) ) 
  : (LKProof, (List[HOLFormula], List[HOLFormula])) = 
    ws._2.contains(aux) match {
      case true => ( proof, (ws._1, ws._2.diff(List(aux)) :+ m) )
      case false => (rule(proof, aux, m), ws)
    }
}
