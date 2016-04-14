package at.logic.gapt.examples.autded
import at.logic.gapt.examples.PigeonHolePrinciple
import at.logic.gapt.expr.Neg
import at.logic.gapt.expr.fol.TseitinCNF
import at.logic.gapt.expr.hol.existsclosure
import at.logic.gapt.proofs.{ Sequent, FOLClause }
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.sat.MiniSAT

object exercise3 {

  println(
    """
  You can obtain a propositional unsatisfiable clause set from the Tseitin-
  transformation of the negation of the n-th pigeonhole principle tautology by:
  gapt> TseitinCNF( Neg( PigeonHolePrinciple( n, n - 1 ) ) )

  Use minisat and prover9 to show that this clause set is unsatisfiable by:
  gapt> Prover9 isUnsat TseitinCNF( Neg( PigeonHolePrinciple( n, n - 1 ) ) )
  and
  gapt> MiniSAT isUnsat TseitinCNF( Neg( PigeonHolePrinciple( n, n - 1 ) ) )

  Use the time-command to find the largest n which is solved in < 5 seconds by 
  prover9 and minisat respectively.
"""
  )
}

