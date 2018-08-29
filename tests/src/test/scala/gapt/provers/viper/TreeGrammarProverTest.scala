package gapt.provers.viper

import gapt.expr._
import gapt.proofs.context.update.InductiveType
import gapt.proofs.SequentMatchers
import gapt.proofs.context.MutableContext
import gapt.provers.escargot.QfUfEscargot
import gapt.provers.maxsat.MaxSat4j
import gapt.provers.viper.grammars.{ TreeGrammarProver, TreeGrammarProverOptions }
import org.specs2.mutable.Specification

class TreeGrammarProverTest extends Specification with SequentMatchers {

  "linear" in {
    implicit val ctx: MutableContext = MutableContext.default()
    ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
    ctx += hoc"p: nat>o"
    val opts = TreeGrammarProverOptions( smtSolver = QfUfEscargot, maxSATSolver = MaxSat4j )
    val sequent = hos"p(0), !x (p(x) -> p(s(x))) :- !x p(x)"
    val prover = new TreeGrammarProver( ctx, sequent, opts )
    val lk = prover.solve()
    lk.endSequent must beMultiSetEqual( sequent )
  }

}
