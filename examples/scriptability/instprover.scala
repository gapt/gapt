import at.logic.gapt.expr.hol.{structuralCNF, univclosure}
import at.logic.gapt.expr._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._
import at.logic.gapt.proofs.expansionTrees.ExpansionProofToLK
import at.logic.gapt.proofs.lk.ExtractInterpolant
import at.logic.gapt.proofs.resolution.expansionProofFromInstances
import at.logic.gapt.proofs.{HOLClause, Sequent}
import at.logic.gapt.provers.sat.Sat4j

import scala.collection.mutable

val endSequent =
  """
    p(0,y)
    p(x,f(y)) -> p(s(x),y)
    p(x,c) -> q(x,g(x))
    q(x,y) -> r(x)
    -r(s(s(s(s(0)))))
  """.split("\n").
  map(_.trim).
  filter(_.nonEmpty).
  map(parseFormula).
  map(univclosure(_)) ++: Sequent()

val (cnf, justifications, definitions) = structuralCNF(endSequent, generateJustifications = true, propositional = false)

val done = mutable.Set[HOLClause]()
val todo = mutable.Queue[HOLClause](cnf.toSeq: _*)
while (Sat4j solve (done ++ todo) isDefined) {
  val next = todo.dequeue()
  todo ++= (for {
    literal1 <- done
    (atom1,index1) <- literal1.zipWithIndex.elements
    (atom2,index2) <- next.zipWithIndex.elements
    if !index1.sameSideAs(index2)
    (mgu1, mgu2) <- syntacticMGU.twoSided(atom1,atom2).toSeq
    newClause <- Seq(literal1.map(mgu1(_)), next.map(mgu2(_)))
  } yield newClause.asInstanceOf[HOLClause])
  done += next
}

val instances =
  for (clause <- cnf) yield
    clause -> (for {
      inst <- done ++ todo
      subst <- syntacticMatching(clause.toFormula, inst.toFormula)
    } yield subst).toSet

val expansionProof = expansionProofFromInstances(instances.toMap, endSequent, justifications, definitions)

val lkProof = ExpansionProofToLK(expansionProof)
println(lkProof)

val (posProof, negProof, interpolant) = ExtractInterpolant(lkProof,
  for (formula <- lkProof.endSequent)
    yield constants(formula).map(_.toString) contains "r")

println(interpolant)

