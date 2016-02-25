import at.logic.gapt.examples.TacticsProof
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Sequent, Context, FiniteContext }

/**
 * Created by sebastian on 2/25/16.
 */
object prime extends TacticsProof {
  implicit var ctx = FiniteContext()
  ctx += Context.Sort( "i" )
  ctx += Context.Sort( "s" )
  ctx += hoc" 0: i"
  ctx += hoc" 1: i"
  ctx += hoc" '+': i > i > i"
  ctx += hoc" '*': i > i > i"
  ctx += hoc" '<': i > i > o"
  ctx += hoc" '=': i > i > o"
  ctx += hoc" 'ν': i > i > s"

  ctx += hoc" in: i > s > o"
  ctx += hoc" set_1: i > s"

  ctx += ( "DIV", le" λl λk ∃m l *m = k" )
  ctx += ( "PRIME", le" λk (1 < k ∧ ∀l(DIV(l,k) -> (l = 1 ∨ l = k)))" )
  ctx += ( "PRE", fof" ∀k (0 < k -> ∃m k = m+1)" )
  ctx += ( "REM", hof" ∀l (0 < l -> ∀m∃k (k < l ∧ in(m, ν(k,l))) )" )
  ctx += ( "PRIME-DIV", hof" ∀m ((¬ m = 1) -> ∃l(PRIME l ∧ DIV l m) )" )

  ctx += ( "subset", le" λX λY ∀n (in(n, X) -> in(n, Y))" )
  ctx += ( "O", le" λX ∀m (in m X -> ∃l subset(ν(m, l+1), X))" )
  ctx += ( "C", le" λX ¬O(X)" )
  ctx += ( "∞", le" λX ∀k ∃l in(k+1+l, X)" )
}