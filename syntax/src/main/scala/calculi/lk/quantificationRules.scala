/*
 * quantificationRules.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.calculi.lk

import propositionalRules._
import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._

package quantificationRules {

  // Quanitifier rules
  case object ForallLeftRuleType extends UnaryRuleTypeA
  case object ForallRightRuleType extends UnaryRuleTypeA
  case object ExistsLeftRuleType extends UnaryRuleTypeA
  case object ExistsRightRuleType extends UnaryRuleTypeA

  object ForallLeftRule {
  }
}
