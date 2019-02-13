package gapt.provers.escargot

import gapt.expr._
import gapt.expr.fol.{ Numeral, folSubTerms }
import gapt.expr.util.syntacticMGU
import gapt.expr.util.syntacticMatching
import gapt.provers.escargot.impl.DiscrTree
import org.specs2.mutable.Specification

class DiscrTreeTest extends Specification {

  val terms = folSubTerms( Set(
    le"x*(y*z) = (x*y)*z", le"x*0 != x*1",
    le"g(g(x1,x2), g(x3,x4))", le"g(x5,x6)",
    le"cons{?a}(u:?a, us:list?a)",
    le"map(x: i>i, cons{i}(a : i, xs : list i))",
    le"map(f: i>i, cons{i}(a : i, xs2 : list i))",
    le"f: i>i",
    le"x: ?a > ?b",
    le"y: list ?a",
    le"z: ?a",
    le"w" ) +
    Numeral( DiscrTree.maxDepth + 5 ) +
    FOLFunctionConst( "s", 1 ).^( DiscrTree.maxDepth )( le"x" ) )

  "test 3" in {
    var tree = DiscrTree[Expr]()
    for ( t <- terms ) tree = tree.insert( t, t )
    for ( t1 <- terms ) {
      val expected = terms.filter( syntacticMatching( _, t1 ).isDefined )
      val actual = tree.generalizations( t1 ).toSet
      val diff = expected diff actual
      require( diff.isEmpty )
      diff must beEmpty
    }
    for ( t1 <- terms ) {
      val expected = terms.filter( syntacticMGU( _, t1 ).isDefined )
      val actual = tree.unifiable( t1 ).toSet
      val diff = expected diff actual
      require( diff.isEmpty )
      diff must beEmpty
    }
    ok
  }

}
