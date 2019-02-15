package gapt.provers.simp

import gapt.expr._
import gapt.expr.formula.Top
import gapt.logic.Polarity
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.TopAxiom
import gapt.proofs.{ HOLSequent, Sequent }
import org.specs2.mutable.Specification

class SimplifierTest extends Specification {

  private def check( seq: HOLSequent ) = {
    val simpLemmas = SimpLemmas.collect( seq.antecedent ++: Sequent() ) + QPropSimpProc
    val simp = Simplifier( simpLemmas.toSeq )
    val res = simp.simpIff( seq.succedent.head, Polarity.InSuccedent )
    res.rhs must_== Top()
    ( CutRule( TopAxiom, res.proof, Top() ).endSequent.distinct diff seq ) must_== Sequent()
  }

  "compute" in {
    check(
      hos"""
           !x x+0=x, !x!y x+s(y)=s(x+y),
           !x d(s(x))=s(s(d(x))), d(0)=0
           :-
           d(s(0)) = s(s(0))
         """ )
  }

  "cond simp" in {
    check( hos"!x (x!=0 -> x/0*x=x), a!=0 :- a=a/0*a" )
  }

  "partially applied functions" in {
    check( hos"f = g, g(c) :- f(c)" )
  }

}
