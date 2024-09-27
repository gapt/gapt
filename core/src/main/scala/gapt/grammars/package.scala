package gapt

import gapt.expr.subst.Substitution
import gapt.expr.{ClosedUnderReplacement, ClosedUnderSub, Const, Expr, TermReplacement, containedNames}

package object grammars {

  implicit object rulesClosedUnderSubstitution extends ClosedUnderSub[Rule] {
    def applySubstitution(sub: Substitution, rule: Rule): Rule = rule(sub)
  }

  implicit object ruleIsReplaceable extends ClosedUnderReplacement[Rule] {
    def replace(rule: Rule, p: PartialFunction[Expr, Expr]) =
      Rule(TermReplacement(rule.lhs, p), TermReplacement(rule.rhs, p))

    def names(rule: Rule) = containedNames(rule.lhs) ++ containedNames(rule.rhs)
  }

  implicit object recSchemIsReplaceable extends ClosedUnderReplacement[RecursionScheme] {
    def replace(rs: RecursionScheme, p: PartialFunction[Expr, Expr]) =
      RecursionScheme(
        TermReplacement(rs.startSymbol, p).asInstanceOf[Const],
        rs.nonTerminals.map(TermReplacement(_, p).asInstanceOf[Const]),
        TermReplacement(rs.rules, p)
      )

    def names(rs: RecursionScheme) =
      containedNames(rs.rules) ++ containedNames(rs.nonTerminals) + rs.startSymbol
  }

}
