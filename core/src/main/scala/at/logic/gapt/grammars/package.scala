package at.logic.gapt

import at.logic.gapt.expr.{ ClosedUnderSub, Substitution }

package object grammars {

  implicit object rulesClosedUnderSubstitution extends ClosedUnderSub[Rule] {
    def applySubstitution( sub: Substitution, rule: Rule ): Rule = rule( sub )
  }

}
