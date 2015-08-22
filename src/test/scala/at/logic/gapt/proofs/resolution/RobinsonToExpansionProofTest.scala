package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr.hol.existsclosure
import at.logic.gapt.proofs.expansionTrees.{ toShallow, toDeep }
import at.logic.gapt.proofs.lk.base.Sequent
import at.logic.gapt.provers.prover9.Prover9Prover
import at.logic.gapt.provers.veriT.VeriTProver
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._
import org.specs2.mutable._

class RobinsonToExpansionProofTest extends Specification {
  val veriT = new VeriTProver
  val p9 = new Prover9Prover()
  if ( !veriT.isInstalled || !p9.isInstalled ) skipAll

  "simple proof from prover9" should {
    val es = existsclosure(
      "P(c,z)" +:
        "P(x,g(z)) -> P(f(x),z) & R(y)" +:
        "P(x,z) -> Q(x)" +:
        Sequent()
        :+ "Q(f(f(x)))"
        map parseFormula
    )

    "extract expansion sequent for the initial clauses" in {
      val Some( robinson ) = p9 getRobinsonProof es
      val expansion = RobinsonToExpansionProof( robinson )
      val deep = toDeep( expansion )
      veriT isValid deep must_== true
    }

    "extract expansion sequent for the given end sequent" in {
      val Some( robinson ) = p9 getRobinsonProof es
      val expansion = RobinsonToExpansionProof( robinson, es )
      toShallow( expansion ) isSubMultisetOf es must_== true
      val deep = toDeep( expansion )
      veriT isValid deep must_== true
    }
  }
}
