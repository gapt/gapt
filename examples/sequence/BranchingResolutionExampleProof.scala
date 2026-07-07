package gapt.examples.sequence

import gapt.expr.*
import gapt.expr.formula.fol.*
import gapt.proofs.*
import gapt.expr.subst.Substitution
import gapt.proofs.resolution.{Input, Resolution, ResolutionProof, Subst}

import scala.collection.mutable

object BranchingResolutionExampleProof {
  /** Creates a refutation of the clause set:
      1) p(x), p(s(x)) ⊢ p(s(s(x)))
      2) p(0) ⊢ 
      3) p(s(0)) ⊢ 
      4)  ⊢ p(s^n(0))

     The proof size is linear in n but will become exponential if it is converted to a cut-free LK proof.
    */
  def apply(n : Int) = {
    val pn = createDerivation(n, mutable.Map[Int, ResolutionProof]())
    Resolution(pn, Suc(0), Input(hos"p(${sn(n)}) ⊢ "), Ant(0))
  }

  val c1 = Input(hos"p(x), p(s(x)) ⊢ p(s(s(x)))")
  val x = fov"x"

  def createDerivation(n: Int, proofs: mutable.Map[Int, ResolutionProof]): ResolutionProof = {
    n match {
      case 0 => proofs.getOrElseUpdate(n, Input(hos"⊢ p(0) "))
      case 1 => proofs.getOrElseUpdate(n, Input(hos"⊢ p(s(0))  "))
      case _ =>
        if proofs contains n then
          proofs(n)
        else {
          val parent1 = createDerivation(n-2, proofs) // derives ⊢ p(n-2)
          val parent2 = createDerivation(n-1, proofs) // derives ⊢ p(n-1)
          val inst_c1 = Subst(c1, Substitution(x,  sn(n-2))) // derives p(n-2), p(n-1) ⊢ p(n)
          val p1 = Resolution(parent1, Suc(0), inst_c1, Ant(0))
          val p2 = Resolution(parent2, Suc(0), p1, Ant(0))
          proofs(n) = p2
          p2
        }
    }
  }

  def sn(n: Int): FOLTerm = if n == 0 then fot"0" else fot"s(${sn(n - 1)})"


}
