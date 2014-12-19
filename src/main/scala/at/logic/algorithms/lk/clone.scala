package at.logic.algorithms.lk

import at.logic.calculi.lk.base.{Sequent, LKProof}
import at.logic.calculi.lk._
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.slk._
import at.logic.language.schema.SchemaFormula
import at.logic.language.hol._
import at.logic.calculi.occurrences._

import scala.collection.immutable.HashMap
import scala.collection.mutable

//creates a copy of an existing LK proof (used for unfolding, not to have cycles in the tree having the base proof several times)
object CloneLKProof {

  def apply(p: LKProof):LKProof = {
    p match {

      case Axiom(ro) => Axiom(ro.antecedent.map(fo => fo.formula.asInstanceOf[HOLFormula]),ro.succedent.map(fo => fo.formula.asInstanceOf[HOLFormula]))

      case AndLeftEquivalenceRule1(p, s, a, m) => {
        val new_p = apply(p)
        AndLeftEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }

      case AndRightEquivalenceRule1(p, s, a, m) => {
        val new_p = apply(p)
        AndRightEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }

      case OrRightEquivalenceRule1(p, s, a, m) => {
        val new_p = apply(p)
        OrRightEquivalenceRule1(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }

      case AndLeftEquivalenceRule3(p, s, a, m) => {
        val new_p = apply(p)
        AndLeftEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }

      case AndRightEquivalenceRule3(p, s, a, m) => {
        val new_p = apply(p)
        AndRightEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }

      case OrRightEquivalenceRule3(p, s, a, m) => {
        val new_p = apply(p)
        OrRightEquivalenceRule3(new_p, a.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])
      }

      case WeakeningLeftRule(p, _, m) => {
        val new_p = apply(p)
        WeakeningLeftRule( new_p, m.formula )
      }

      case WeakeningRightRule(p, _, m) => {
        val new_p = apply(p)
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
        AndLeft1Rule( new_p, a.formula, a2)
      }

      case AndLeft2Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case And(l, _) => l }
        AndLeft2Rule( new_p, a2, a.formula )
      }

      case OrRight1Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case Or(_, r) => r }
        OrRight1Rule( new_p, a.formula, a2)
      }

      case OrRight2Rule(p, r, a, m) =>  {
        val new_p = apply(p)
        val a2 = m.formula  match { case Or(l, _) => l }
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

      case EquationLeft1Rule(up1, up2, _, eqocc, auxocc,_, prin) => {
        val new_p1 = apply(up1)
        val new_p2 = apply(up2)
        EquationLeftRule(new_p1, new_p2, eqocc.formula, auxocc.formula, prin.formula)
      }

      case EquationLeft2Rule(up1, up2, _, eqocc, auxocc,_, prin) => {
        val new_p1 = apply(up1)
        val new_p2 = apply(up2)
        EquationLeftRule(new_p1, new_p2, eqocc.formula, auxocc.formula, prin.formula)
      }

      case EquationRight1Rule(up1, up2, _, eqocc, auxocc,_, prin) => {
        val new_p1 = apply(up1)
        val new_p2 = apply(up2)
        EquationRightRule(new_p1, new_p2, eqocc.formula, auxocc.formula, prin.formula)
      }

      case EquationRight2Rule(up1, up2, _, eqocc, auxocc,_, prin) => {
        val new_p1 = apply(up1)
        val new_p2 = apply(up2)
        EquationRightRule(new_p1, new_p2, eqocc.formula, auxocc.formula, prin.formula)
      }

      case DefinitionLeftRule(up, _, aux, prin) => {
        val new_p = apply(up)
        DefinitionLeftRule(new_p, aux.formula, prin.formula)
      }

      case DefinitionRightRule(up, _, aux, prin) => {
        val new_p = apply(up)
        DefinitionRightRule(new_p, aux.formula, prin.formula)
      }

      case ForallLeftRule(p, seq, a, m, t) => {
        val new_parent = apply(p)
        ForallLeftRule(new_parent, a.formula, m.formula, t)
      }

      case ForallRightRule(p, seq, a, m, t) => {
        val new_parent = apply(p)
        ForallRightRule(new_parent, a.formula, m.formula, t)
      }

      case ExistsLeftRule(p, seq, a, m, v) => {
        val new_parent = apply(p)
        ExistsLeftRule(new_parent, a.formula, m.formula, v)
      }

      case ExistsRightRule(p, seq, a, m, t) => {
        val new_parent = apply(p)
        ExistsRightRule(new_parent, a.formula, m.formula, t)
      }

      case u => throw new UnfoldException("Rule is not supported: " + u.rule)
    }}

  /** Same as apply, but in addition to the cloned proof it returns a map between formula occurrences of the old and new proofs.
   *
   * @param proof An LKProof.
   * @param factory An FOFactory.
   * @return A pair consisting of the cloned proof and a map between old and new formula occurrences.
   */
  def withMap(proof: LKProof)(implicit factory: FOFactory): (LKProof, Map[FormulaOccurrence, FormulaOccurrence]) = {
    proof match {

      case Axiom(ro) =>
        var occMap = new HashMap[FormulaOccurrence, FormulaOccurrence]()
        val antNew: Seq[FormulaOccurrence] = ro.antecedent map (_.formula) map (x => factory.createFormulaOccurrence(x, Nil))
        val sucNew: Seq[FormulaOccurrence] = ro.succedent map (_.formula) map (x => factory.createFormulaOccurrence(x, Nil))

        // Add the pairs of old and new occurrences to the map
        occMap = (ro.antecedent, antNew).zipped.foldLeft(occMap)(_ + _)
        occMap = (ro.succedent, sucNew).zipped.foldLeft(occMap)(_ + _)
        
        (Axiom(Sequent(antNew, sucNew)), occMap)

      case AndLeftEquivalenceRule1(p,_, a, m) =>
        val (pCloned, map) = withMap(p)
        val aNew = map(a)
        val proofCloned = AndLeftEquivalenceRule1(pCloned, aNew.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case AndRightEquivalenceRule1(p,_, a, m) =>
        val (pCloned, map) = withMap(p)
        val aNew = map(a)
        val proofCloned = AndRightEquivalenceRule1(pCloned, aNew.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case OrRightEquivalenceRule1(p,_, a, m) =>
        val (pCloned, map) = withMap(p)
        val aNew = map(a)
        val proofCloned = OrRightEquivalenceRule1(pCloned, aNew.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case AndLeftEquivalenceRule3(p,_, a, m) =>
        val (pCloned, map) = withMap(p)
        val aNew = map(a)
        val proofCloned = AndLeftEquivalenceRule3(pCloned, aNew.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case AndRightEquivalenceRule3(p,_, a, m) =>
        val (pCloned, map) = withMap(p)
        val aNew = map(a)
        val proofCloned = AndRightEquivalenceRule3(pCloned, aNew.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case OrRightEquivalenceRule3(p,_, a, m) =>
        val (pCloned, map) = withMap(p)
        val aNew = map(a)
        val proofCloned = AndLeftEquivalenceRule3(pCloned, aNew.formula.asInstanceOf[SchemaFormula], m.formula.asInstanceOf[SchemaFormula])

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case WeakeningLeftRule(p,_, m) =>
        val (pCloned, map) = withMap(p)
        val proofCloned = WeakeningLeftRule(pCloned, m.formula)

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case WeakeningRightRule(p,_, m) =>
        val (pCloned, map) = withMap(p)
        val proofCloned = WeakeningRightRule(pCloned, m.formula)

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case CutRule(p1, p2,_, a1, a2) =>
        val (p1Cloned, map1) = withMap(p1)
        val (p2Cloned, map2) = withMap(p2)
        val (a1New, a2New) = (map1(a1), map2(a2))
        val proofCloned = CutRule(p1Cloned, p2Cloned, a1New, a2New)

        var mapNew = map1 ++ map2
        mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(mapNew)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case OrLeftRule(p1, p2, _, a1, a2, m) =>
        val (p1Cloned, map1) = withMap(p1)
        val (p2Cloned, map2) = withMap(p2)
        val (a1New, a2New) = (map1(a1), map2(a2))
        val proofCloned = OrLeftRule(p1Cloned, p2Cloned, a1New, a2New)

        var mapNew = map1 ++ map2
        mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(mapNew)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case AndRightRule(p1, p2, _, a1, a2, m) =>
        val (p1Cloned, map1) = withMap(p1)
        val (p2Cloned, map2) = withMap(p2)
        val (a1New, a2New) = (map1(a1), map2(a2))
        val proofCloned = AndRightRule(p1Cloned, p2Cloned, a1New, a2New)

        var mapNew = map1 ++ map2
        mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(mapNew)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case NegLeftRule( p, _, a, m ) =>
        val (pCloned, map) = withMap(p)
        val aNew = map(a)
        val proofCloned = NegLeftRule(pCloned, aNew)

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case AndLeft1Rule(p,_, a, m) =>
        val (pCloned, map) = withMap(p)
        val a2 = m.formula  match { case And(_, r) => r }
        val aNew = map(a)
        val proofCloned = AndLeft1Rule(pCloned, aNew, a2)

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case AndLeft2Rule(p,_, a, m) =>
        val (pCloned, map) = withMap(p)
        val a2 = m.formula  match { case And(l,_) => l }
        val aNew = map(a)
        val proofCloned = AndLeft2Rule(pCloned, a2, aNew)

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case OrRight1Rule(p,_, a, m) =>
        val (pCloned, map) = withMap(p)
        val a2 = m.formula  match { case And(_, r) => r }
        val aNew = map(a)
        val proofCloned = OrRight1Rule(pCloned, aNew, a2)

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case OrRight2Rule(p,_, a, m) =>
        val (pCloned, map) = withMap(p)
        val a2 = m.formula  match { case And(l,_) => l }
        val aNew = map(a)
        val proofCloned = OrRight2Rule(pCloned, a2, aNew)

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case NegRightRule( p, _, a, m ) =>
        val (pCloned, map) = withMap(p)
        val aNew = map(a)
        val proofCloned = NegRightRule(pCloned, aNew)

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case ContractionLeftRule(p, _, a1, a2, m) =>
        val (pCloned, map) = withMap(p)
        val (a1New, a2New) = (map(a1), map(a2))
        val proofCloned = ContractionLeftRule(pCloned, a1New, a2New)

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case ContractionRightRule(p, _, a1, a2, m) =>
        val (pCloned, map) = withMap(p)
        val (a1New, a2New) = (map(a1), map(a2))
        val proofCloned = ContractionRightRule(pCloned, a1New, a2New)

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case ImpLeftRule(p1, p2, _, a1, a2, m) =>
        val (p1Cloned, map1) = withMap(p1)
        val (p2Cloned, map2) = withMap(p2)
        val (a1New, a2New) = (map1(a1), map2(a2))
        val proofCloned = ImpLeftRule(p1Cloned, p2Cloned, a1New, a2New)

        var mapNew = map1 ++ map2
        mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(mapNew)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case ImpRightRule(p, _, a1, a2, m) =>
        val (pCloned, map) = withMap(p)
        val (a1New, a2New) = (map(a1), map(a2))
        val proofCloned = ImpRightRule(pCloned, a1New, a2New)

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case EquationLeft1Rule(up1, up2, _, eqocc, auxocc,_, prin) =>
        val (up1Cloned, map1) = withMap(up1)
        val (up2Cloned, map2) = withMap(up2)
        val (eqNew, auxNew) = (map1(eqocc), map2(auxocc))
        val proofCloned = EquationLeft1Rule(up1Cloned, up2Cloned, eqNew, auxNew, prin.formula)

        var mapNew = map1 ++ map2
        mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(mapNew)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case EquationLeft2Rule(up1, up2, _, eqocc, auxocc,_, prin) =>
        val (up1Cloned, map1) = withMap(up1)
        val (up2Cloned, map2) = withMap(up2)
        val (eqNew, auxNew) = (map1(eqocc), map2(auxocc))
        val proofCloned = EquationLeft2Rule(up1Cloned, up2Cloned, eqNew, auxNew, prin.formula)

        var mapNew = map1 ++ map2
        mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(mapNew)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case EquationRight1Rule(up1, up2, _, eqocc, auxocc,_, prin) =>
        val (up1Cloned, map1) = withMap(up1)
        val (up2Cloned, map2) = withMap(up2)
        val (eqNew, auxNew) = (map1(eqocc), map2(auxocc))
        val proofCloned = EquationRight1Rule(up1Cloned, up2Cloned, eqNew, auxNew, prin.formula)

        var mapNew = map1 ++ map2
        mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(mapNew)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case EquationRight2Rule(up1, up2, _, eqocc, auxocc,_, prin) =>
        val (up1Cloned, map1) = withMap(up1)
        val (up2Cloned, map2) = withMap(up2)
        val (eqNew, auxNew) = (map1(eqocc), map2(auxocc))
        val proofCloned = EquationRight1Rule(up1Cloned, up2Cloned, eqNew, auxNew, prin.formula)

        var mapNew = map1 ++ map2
        mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(mapNew)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case DefinitionLeftRule(p,_, a, prin) =>
        val (pCloned, map) = withMap(p)
        val aNew = map(a)
        val proofCloned = DefinitionLeftRule(pCloned, aNew, prin.formula)

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case DefinitionRightRule(p,_, a, prin) =>
        val (pCloned, map) = withMap(p)
        val aNew = map(a)
        val proofCloned = DefinitionRightRule(pCloned, aNew, prin.formula)

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case ForallLeftRule(p,_, a, m, t) =>
        val (pCloned, map) = withMap(p)
        val aNew = map(a)
        val proofCloned = ForallLeftRule(pCloned, aNew, m.formula, t)

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case ForallRightRule(p,_, a, m, v) =>
        val (pCloned, map) = withMap(p)
        val aNew = map(a)
        val proofCloned = ForallRightRule(pCloned, aNew, m.formula, v)

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case ExistsLeftRule(p, seq, a, m, v) =>
        val (pCloned, map) = withMap(p)
        val aNew = map(a)
        val proofCloned = ExistsLeftRule(pCloned, aNew, m.formula, v)

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case ExistsRightRule(p,_, a, m, t) =>
        val (pCloned, map) = withMap(p)
        val aNew = map(a)
        val proofCloned = ExistsRightRule(pCloned, aNew, m.formula, t)

        var mapNew = (proof.root.antecedent, proofCloned.root.antecedent).zipped.foldLeft(map)(_ + _)
        mapNew = (proof.root.succedent, proofCloned.root.succedent).zipped.foldLeft(mapNew)(_ + _)
        (proofCloned, mapNew)

      case u => throw new UnfoldException("Rule is not supported: " + u.rule)
    }}
}


class UnfoldException(msg: String) extends Exception(msg)
