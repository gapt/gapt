package at.logic.algorithms.lk

import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences._
import at.logic.language.hol._
import at.logic.language.hol.BetaReduction._
import ProofTransformationUtils.computeMap

object applySubstitution {

  // TODO: finish refactoring rules like this! there is still redundancy in handleRule!
  def handleWeakening( new_parent: (LKProof, Map[FormulaOccurrence, FormulaOccurrence]),
                       subst: Substitution,
                       old_parent: LKProof,
                       old_proof: LKProof,
                       constructor: (LKProof, HOLFormula) => LKProof with PrincipalFormulas,
                       m: FormulaOccurrence ) = {
     val new_proof = constructor( new_parent._1, betaNormalize(subst(m.formula)) )
    ( new_proof, computeMap( old_parent.root.antecedent ++ old_parent.root.succedent, old_proof, new_proof, new_parent._2 ) + ((m, new_proof.prin.head )) )
  }
  def handleContraction( new_parent: (LKProof, Map[FormulaOccurrence, FormulaOccurrence]),
                         old_parent: LKProof,
                         old_proof: LKProof,
                         a1: FormulaOccurrence,
                         a2: FormulaOccurrence,
                         constructor: (LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof) = {
    val new_proof = constructor( new_parent._1, new_parent._2( a1 ), new_parent._2( a2 ) )
    ( new_proof, computeMap( old_parent.root.antecedent ++ old_parent.root.succedent, old_proof, new_proof, new_parent._2 ) )
  }
  def handleBinaryProp( new_parent_1: (LKProof, Map[FormulaOccurrence, FormulaOccurrence]),
                        new_parent_2: (LKProof, Map[FormulaOccurrence, FormulaOccurrence]),
                        a1: FormulaOccurrence,
                        a2: FormulaOccurrence,
                        old_parent_1: LKProof,
                        old_parent_2: LKProof,
                        old_proof: LKProof,
                        constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence) => LKProof) = {
    val new_proof = constructor( new_parent_1._1, new_parent_2._1, new_parent_1._2( a1 ), new_parent_2._2( a2 ) )
    ( new_proof, computeMap( old_parent_1.root.antecedent ++ old_parent_1.root.succedent ++ old_parent_2.root.antecedent ++ old_parent_2.root.succedent,
      old_proof, new_proof, new_parent_1._2 ++ new_parent_2._2 ) )
  }

  def handleEquationRule(
    constructor: (LKProof, LKProof, FormulaOccurrence, FormulaOccurrence, HOLFormula) => LKProof,
    p1: LKProof,
    p2: LKProof,
    old_proof: LKProof,
    new_p1: (LKProof, Map[FormulaOccurrence, FormulaOccurrence]),
    new_p2: (LKProof, Map[FormulaOccurrence, FormulaOccurrence]),
    s: Sequent,
    a1: FormulaOccurrence,
    a2: FormulaOccurrence,
    m: HOLFormula ) = {
      val new_proof = constructor( new_p1._1, new_p2._1, a1, a2, m )
      ( new_proof, computeMap( p1.root.antecedent ++ p1.root.succedent ++ p2.root.antecedent ++ p2.root.succedent,
        old_proof, new_proof, new_p1._2 ++ new_p2._2 ) )
  }

  def handleRule( proof: LKProof, new_parents: List[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])],
                  subst: Substitution ) : (LKProof, Map[FormulaOccurrence, FormulaOccurrence]) = {
    proof match {
      case Axiom(so) => {
        val ant_occs = so.antecedent
        val succ_occs = so.succedent
        val a = Axiom(ant_occs.map( fo => betaNormalize( subst(fo.formula)) ) ,
          succ_occs.map( fo => betaNormalize( subst(fo.formula) ) ) )
        require(a.root.antecedent.length >= ant_occs.length, "cannot create translation map: old proof antecedent is shorter than new one")
        require(a.root.succedent.length >= succ_occs.length, "cannot create translation map: old proof succedent is shorter than new one")
        val map = Map[FormulaOccurrence, FormulaOccurrence]() ++
          (ant_occs zip a.root.antecedent) ++ (succ_occs zip a.root.succedent)
        (a, map)
      }
      case WeakeningLeftRule(p, s, m) => handleWeakening( new_parents.head, subst, p, proof, WeakeningLeftRule.apply, m )
      case WeakeningRightRule(p, s, m) => handleWeakening( new_parents.head, subst, p, proof, WeakeningRightRule.apply, m )
      case ContractionLeftRule(p, s, a1, a2, m) => handleContraction( new_parents.head, p, proof, a1, a2, ContractionLeftRule.apply )
      case ContractionRightRule(p, s, a1, a2, m) => handleContraction( new_parents.head, p, proof, a1, a2, ContractionRightRule.apply )
      case CutRule(p1, p2, s, a1, a2) => {
        val new_p1 = new_parents.head
        val new_p2 = new_parents.last
        val new_proof = CutRule( new_p1._1, new_p2._1, new_p1._2( a1 ), new_p2._2( a2 ) )
        ( new_proof, computeMap(
          p1.root.antecedent ++ (p1.root.succedent.filter(_ != a1)) ++
          (p2.root.antecedent.filter(_ != a2)) ++ p2.root.succedent,
          proof, new_proof, new_p1._2 ++ new_p2._2 ) )
      }
      case AndRightRule(p1, p2, s, a1, a2, m) => handleBinaryProp( new_parents.head, new_parents.last, a1, a2, p1, p2, proof, AndRightRule.apply )
      case AndLeft1Rule(p, s, a, m) => {
        val f = m.formula match { case And(_, w) => w }
        val new_parent = new_parents.head
        val new_proof = AndLeft1Rule( new_parent._1, new_parent._2( a ), betaNormalize(subst( f )) )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case AndLeft2Rule(p, s, a, m) => {
        val f = m.formula match { case And(w, _) => w }
        val new_parent = new_parents.head
        val new_proof = AndLeft2Rule( new_parent._1, betaNormalize(subst( f )), new_parent._2( a ) )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case OrLeftRule(p1, p2, s, a1, a2, m) => handleBinaryProp( new_parents.head, new_parents.last, a1, a2, p1, p2, proof, OrLeftRule.apply )
      case OrRight1Rule(p, s, a, m) => {
        val f = m.formula match { case Or(_, w) => w }
        val new_parent = new_parents.head
        val new_proof = OrRight1Rule( new_parent._1, new_parent._2( a ), betaNormalize(subst( f )) )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case OrRight2Rule(p, s, a, m) => {
        val f = m.formula match { case Or(w, _) => w }
        val new_parent = new_parents.head
        val new_proof = OrRight2Rule( new_parent._1, betaNormalize(subst( f )), new_parent._2( a ) )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case ImpLeftRule(p1, p2, s, a1, a2, m) => {
        val new_p1 = new_parents.head
        val new_p2 = new_parents.last
        val new_proof = ImpLeftRule( new_p1._1, new_p2._1, new_p1._2( a1 ), new_p2._2( a2 ) )
        ( new_proof, computeMap( p1.root.antecedent ++ p1.root.succedent ++ p2.root.antecedent ++ p2.root.succedent,
          proof, new_proof, new_p1._2 ++ new_p2._2 ) )
      }
      case ImpRightRule(p, s, a1, a2, m) => {
        val new_parent = new_parents.head
        val new_proof = ImpRightRule( new_parent._1,
                                      new_parent._2( a1 ),
                                      new_parent._2( a2 ) )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case NegLeftRule(p, s, a, m) => {
        val new_parent = new_parents.head
        val new_proof = NegLeftRule( new_parent._1, new_parent._2( a ) )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case NegRightRule(p, s, a, m) => {
        val new_parent = new_parents.head
        val new_proof = NegRightRule( new_parent._1, new_parent._2( a ) )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case DefinitionRightRule( p, s, a, m ) => {
        val new_parent = new_parents.head
        val new_proof = DefinitionRightRule( new_parent._1, new_parent._2( a ), betaNormalize(subst( m.formula )) )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case DefinitionLeftRule( p, s, a, m ) => {
        val new_parent = new_parents.head
        val new_proof = DefinitionLeftRule( new_parent._1, new_parent._2( a ), betaNormalize(subst( m.formula )) )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case EquationLeft1Rule( p1, p2, s, a1, a2, _, m ) =>
        handleEquationRule( EquationLeftMacroRule.apply, p1, p2, proof, new_parents.head, new_parents.last, s,
          new_parents.head._2( a1 ), new_parents.last._2( a2 ),
          betaNormalize(subst( m.formula )) )
      case EquationLeft2Rule( p1, p2, s, a1, a2, _, m ) =>
        handleEquationRule( EquationLeftMacroRule.apply, p1, p2, proof, new_parents.head, new_parents.last, s,
          new_parents.head._2( a1 ), new_parents.last._2( a2 ),
          betaNormalize(subst( m.formula )) )
      case EquationRight1Rule( p1, p2, s, a1, a2, _, m ) =>
        handleEquationRule( EquationRightMacroRule.apply, p1, p2, proof, new_parents.head, new_parents.last, s,
          new_parents.head._2( a1 ), new_parents.last._2( a2 ),
          betaNormalize(subst( m.formula )) )
      case EquationRight2Rule( p1, p2, s, a1, a2, _, m ) =>
        handleEquationRule( EquationRightMacroRule.apply, p1, p2, proof, new_parents.head, new_parents.last, s,
          new_parents.head._2( a1 ), new_parents.last._2( a2 ),
          betaNormalize(subst( m.formula )) )
      case ForallLeftRule( p, s, a, m, t ) => {
        val new_parent = new_parents.head
        val new_proof = ForallLeftRule( new_parent._1, new_parent._2( a ), betaNormalize(subst( m.formula )), betaNormalize(subst( t )) )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
    }
      case ExistsRightRule( p, s, a, m, t ) => {
        val new_parent = new_parents.head
        val new_proof = ExistsRightRule( new_parent._1, new_parent._2( a ), betaNormalize(subst( m.formula )), betaNormalize(subst( t )) )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case ExistsLeftRule( p, s, a, m, v ) => {
        assert( !subst.map.contains( v ) )
        val new_parent = new_parents.head
        val new_proof = ExistsLeftRule( new_parent._1, new_parent._2( a ), betaNormalize(subst( m.formula )), v )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case ForallRightRule( p, s, a, m, v ) => {
        assert( !subst.map.contains( v ) )
        val new_parent = new_parents.head
        val new_proof = ForallRightRule( new_parent._1, new_parent._2( a ), betaNormalize(subst( m.formula )), v )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
/*
      case ForallSkLeftRule( p, s, a, m, t ) => {
        val new_parent = new_parents.head
        val label_removed = m.skolem_label.diff(a.skolem_label).nonEmpty || a.skolem_label.diff(m.skolem_label).nonEmpty
        val new_proof = ForallSkLeftRule( new_parent._1, new_parent._2( a ).asInstanceOf[LabelledFormulaOccurrence], subst.applyAndBetaNormalize( m.formula ).asInstanceOf[HOLFormula], subst.applyAndBetaNormalize( t ), label_removed )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case ExistsSkRightRule( p, s, a, m, t ) => {
        val new_parent = new_parents.head
        val label_removed = m.skolem_label.diff(a.skolem_label).nonEmpty || a.skolem_label.diff(m.skolem_label).nonEmpty
        val new_proof = ExistsSkRightRule( new_parent._1, new_parent._2( a ).asInstanceOf[LabelledFormulaOccurrence], subst.applyAndBetaNormalize( m.formula ).asInstanceOf[HOLFormula], subst.applyAndBetaNormalize( t ), label_removed )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case ExistsSkLeftRule( p, s, a, m, v ) => {
        val new_parent = new_parents.head
        val new_proof = ExistsSkLeftRule( new_parent._1, new_parent._2( a ).asInstanceOf[LabelledFormulaOccurrence], subst.applyAndBetaNormalize( m.formula ).asInstanceOf[HOLFormula], v )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
      case ForallSkRightRule( p, s, a, m, v ) => {
        val new_parent = new_parents.head
        val new_proof = ForallSkRightRule( new_parent._1, new_parent._2( a ).asInstanceOf[LabelledFormulaOccurrence], subst.applyAndBetaNormalize( m.formula ).asInstanceOf[HOLFormula], v )
        ( new_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, new_proof, new_parent._2 ) )
      }
 */
    }
  }

  def apply( proof: LKProof, subst: Substitution ) : (LKProof, Map[FormulaOccurrence, FormulaOccurrence]) =
    proof match {
      case Axiom(_) => handleRule( proof, Nil, subst )
      case UnaryLKProof(_, p, _, _, _) => handleRule( proof, apply( p, subst )::Nil, subst )
//      case UnaryLKSKProof(_, p, _, _, _) => handleRule( proof, apply( p, subst )::Nil, subst )
      case BinaryLKProof(_, p1, p2, _, _, _, _) =>
        handleRule( proof, apply( p1, subst )::apply( p2, subst )::Nil, subst )
    }

}
