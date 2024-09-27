package gapt.proofs.lk.rules.macros

import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Eq
import gapt.expr.formula.Imp
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLVar
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.LogicalAxiom

object TransRule {

  /**
   * Performs a proof employing transitivity.
   *
   * Takes a proof π with end-sequent of the form
   * <pre>
   * (x=z), Trans, ... |- ...
   * </pre>
   * and return one with end-sequent of the form
   * <pre>
   * (x=y), (y=z), Trans, ... |- ...
   * </pre>
   * where Trans is defined as Forall xyz.((x=y ∧ y=z) -> x=z)
   *
   * @param x a first-order term
   * @param y a first-order term
   * @param z a first-order term
   * @param subProof The proof π which contains the (x=z) which is to be shown.
   * @return A proof with π as a subtree and the formula (x=z) replaced by (x=y) and (y=z).
   */
  def apply(x: FOLTerm, y: FOLTerm, z: FOLTerm, subProof: LKProof): LKProof = {

    val xv = FOLVar("x")
    val yv = FOLVar("y")
    val zv = FOLVar("z")

    // Forall xyz.(x = y ^ y = z -> x = z)
    val Trans = All(xv, All(yv, All(zv, Imp(And(Eq(xv, yv), Eq(yv, zv)), Eq(xv, zv)))))
    def TransX(x: FOLTerm) = All(yv, All(zv, Imp(And(Eq(x, yv), Eq(yv, zv)), Eq(x, zv))))
    def TransXY(x: FOLTerm, y: FOLTerm) = All(zv, Imp(And(Eq(x, y), Eq(y, zv)), Eq(x, zv)))
    def TransXYZ(x: FOLTerm, y: FOLTerm, z: FOLTerm) = Imp(And(Eq(x, y), Eq(y, z)), Eq(x, z))

    val xy = Eq(x, y)
    val yz = Eq(y, z)
    val xz = Eq(x, z)

    val ax_xy = LogicalAxiom(xy)
    val ax_yz = LogicalAxiom(yz)

    val s1 = AndRightRule(ax_xy, xy, ax_yz, yz)

    val imp = ImpLeftRule(s1, And(xy, yz), subProof, xz)

    val allQZ = ForallLeftRule(imp, TransXY(x, y), z)
    val allQYZ = ForallLeftRule(allQZ, TransX(x), y)
    val allQXYZ = ForallLeftRule(allQYZ, Trans, x)

    ContractionLeftRule(allQXYZ, Trans)
  }
}
