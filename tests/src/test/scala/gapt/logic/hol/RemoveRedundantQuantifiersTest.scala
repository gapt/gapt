package gapt.logic.hol

import gapt.expr._
import org.specs2.mutable.Specification
import org.specs2.specification.core.Fragment

class RemoveRedundantQuantifiersTest extends Specification {
  "removeRedundantQuantifiers" should {
    def removeRedundantQuantifiersIn[T <: Expr]( expression: T, expectedExpression: T ): Fragment = {
      s"remove redundant quantifiers in $expression to get $expectedExpression" in {
        removeRedundantQuantifiers( expression ) must beEqualTo( expectedExpression )
      }
    }

    def notRemoveQuantifiersIn[T <: Expr]( expression: T ): Fragment = {
      s"not remove quantifiers in $expression" in {
        removeRedundantQuantifiers( expression ) must beEqualTo( expression )
      }
    }

    notRemoveQuantifiersIn( hof"!x R(x)" )
    removeRedundantQuantifiersIn( hof"!x R(a)", le"R(a):o" )
    removeRedundantQuantifiersIn( hof"(!x R(a)) | R(x)", hof"R(a) | R(x)" )
    removeRedundantQuantifiersIn( hof"(!x R(x)) & (!x R(a))", hof"(!x R(x)) & R(a)" )
    removeRedundantQuantifiersIn( hof"?x R(?y S(a), T(x))", hof"?x R(S(a): o, T(x))" )
    removeRedundantQuantifiersIn( le"!t (^x R(x, t) & ?y S(b, t))(!s T(a))", le"!t (^x R(x, t) & S(b, t))(T(a):o)" )
  }
}
