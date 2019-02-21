package gapt.proofs.expansion

import gapt.expr._
import gapt.expr.fol.Numeral
import gapt.expr.hol.containsQuantifierOnLogicalLevel
import gapt.proofs.lk.util.isMaeharaMG3i
import gapt.proofs.{ Sequent, SequentMatchers }
import gapt.provers.escargot.Escargot
import org.specs2.matcher.Matcher
import org.specs2.mutable.Specification

class ExpansionProofToMG3iViaSATTest extends Specification with SequentMatchers {

  def ep( f: Formula ): ExpansionProof =
    if ( containsQuantifierOnLogicalLevel( f ) )
      Escargot.withDeskolemization.getExpansionProof( f ).get
    else
      ExpansionProof( Sequent() :+ formulaToExpansionTree( f, Polarity.InSuccedent ) )

  def beGood: Matcher[ExpansionProof] =
    ( e: ExpansionProof ) => ExpansionProofToMG3iViaSAT( e ) must beLike {
      case Right( lk ) =>
        isMaeharaMG3i( lk ) must_== true
        lk.endSequent must beSetEqual( e.shallow )
    }

  "not not lem" in { ep( hof"~ ~(p | ~p)" ) must beGood }
  "and imp iff" in { ep( hof"(p & q -> r) <-> (p -> q -> r)" ) must beGood }
  "not p iff not p" in { ep( hof"~(p <-> ~p)" ) must beGood }
  "not iff imp false" in { ep( hof"~p <-> (p -> false)" ) must beGood }
  "not not imp lem" in { ep( hof"~ ~ (E -> p | ~p)" ) must beGood }
  "linear" in { ep( hof"!x P(x,0) & !x!y (!z P(f(x,z),y) -> P(x,s(y))) -> !x P(x,${Numeral( 4 )})" ) must beGood }

  "cond dec" in { ep( hof"(q -> p | ~p) -> q -> ~p | (r -> r & p)" ) must beGood }

}
