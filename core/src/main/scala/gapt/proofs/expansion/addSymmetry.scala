package gapt.proofs.expansion

import gapt.expr._
import gapt.expr.formula.Eq
import gapt.expr.formula.fol._
import gapt.expr.subst.Substitution
import gapt.logic.Polarity

/**
 * Given an expansion sequent S which is a tautology modulo symmetry of equality,
 * returns an expansion sequent S' which is S extended by the symmetry instances
 * needed to make it a tautology.
 */
object addSymmetry {

  def apply(s: ExpansionSequent): ExpansionSequent = {
    val negativePairs = for (et <- s.elements.view; case ETAtom(Eq(l, r), Polarity.Negative) <- et.subProofs) yield l -> r
    val positivePairs = for (et <- s.elements.view; case ETAtom(Eq(l, r), Polarity.Positive) <- et.subProofs) yield l -> r

    positivePairs.map(_.swap).toSet.intersect(negativePairs.toSet).groupBy(_._1.ty).map {
      case (ty, pairs) =>
        val Seq(x, y) = Seq("x", "y").map(Var(_, ty))
        val symmAx = hof"!$x !$y ($x=$y -> $y=$x)"
        formulaToExpansionTree(
          symmAx,
          pairs.map { case (l, r) => Substitution(x -> l, y -> r) },
          Polarity.InAntecedent
        )
    } ++: s
  }

}
