package at.logic.calculi.slk

import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences._

  package base {

    trait sLKProof extends LKProof


  }

//-----------------------------------------------------------------------------------------------

  package propositionalRules {

    import at.logic.calculi.lk.propositionalRules._
    import at.logic.calculi.proofs._


    case object BigAndRightRuleType extends BinaryRuleTypeA
    case object BigAndLeft1RuleType extends UnaryRuleTypeA
    case object BigAndLeft2RuleType extends UnaryRuleTypeA
    case object BigOrRight1RuleType extends UnaryRuleTypeA
    case object BigOrRight2RuleType extends UnaryRuleTypeA
    case object BigOrLeftRuleType extends BinaryRuleTypeA


  }












