package at.logic.gapt

import at.logic.gapt.expr.{ ClosedUnderReplacement, ClosedUnderSub, Const, LambdaExpression, Substitution, TermReplacement, containedNames }

package object grammars {

  implicit object rulesClosedUnderSubstitution extends ClosedUnderSub[Rule] {
    def applySubstitution( sub: Substitution, rule: Rule ): Rule = rule( sub )
  }

  implicit object ruleIsReplaceable extends ClosedUnderReplacement[Rule] {
    def replace( rule: Rule, p: PartialFunction[LambdaExpression, LambdaExpression] ) =
      Rule( TermReplacement( rule.lhs, p ), TermReplacement( rule.rhs, p ) )

    def names( rule: Rule ) = containedNames( rule.lhs ) ++ containedNames( rule.rhs )
  }

  implicit object recSchemIsReplacable extends ClosedUnderReplacement[RecursionScheme] {
    def replace( rs: RecursionScheme, p: PartialFunction[LambdaExpression, LambdaExpression] ) =
      RecursionScheme(
        TermReplacement( rs.startSymbol, p ).asInstanceOf[Const],
        rs.nonTerminals.map( TermReplacement( _, p ).asInstanceOf[Const] ),
        TermReplacement( rs.rules, p )
      )

    def names( rs: RecursionScheme ) =
      containedNames( rs.rules ) ++ containedNames( rs.nonTerminals ) + rs.startSymbol
  }

}
