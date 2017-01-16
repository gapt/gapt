package at.logic.gapt.examples

import at.logic.gapt.examples.tip.grammars._
import at.logic.gapt.examples.tip.isaplanner._
import at.logic.gapt.formats.tip.TipSmtParser
import org.specs2.mutable.Specification

class TipProofsTests extends Specification {

  def requireTip( test: => Any ) = {
    if ( TipSmtParser.isInstalled ) {
      test
    } else {
      "tip not installed" in skipped( "tip tool is not installed" )
    }
  }

  // grammars
  requireTip { "grammars/simp_expr_unambig1" in { simp_expr_unambig1; ok } }

  // isaplanner
  requireTip { "isaplanner/prop_03" in { prop_03; ok } }
  "isaplanner/prop_06" in { prop_06; ok }

  requireTip { "isaplanner/prop_07" in { prop_07; ok } }
  requireTip { "isaplanner/prop_08" in { prop_08; ok } }
  requireTip { "isaplanner/prop_09" in { prop_09; ok } }
  requireTip { "isaplanner/prop_10" in { prop_10; ok } }
  requireTip { "isaplanner/prop_11" in { prop_11; ok } }
  requireTip { "isaplanner/prop_12" in { prop_12; ok } }
  requireTip { "isaplanner/prop_13" in { prop_13; ok } }
  requireTip { "isaplanner/prop_14" in { prop_14; ok } }
  requireTip { "isaplanner/prop_15" in { prop_15; ok } }
  requireTip { "isaplanner/prop_16" in { prop_16; ok } }
  requireTip { "isaplanner/prop_17" in { prop_17; ok } }
  requireTip { "isaplanner/prop_18" in { prop_18; ok } }
  requireTip { "isaplanner/prop_19" in { prop_19; ok } }

  requireTip { "isaplanner/prop_21" in { prop_21; ok } }
  requireTip { "isaplanner/prop_22" in { prop_22; ok } }
  requireTip { "isaplanner/prop_23" in { prop_23; ok } }
  requireTip { "isaplanner/prop_24" in { prop_24; ok } }

  requireTip { "isaplanner/prop_26" in { prop_26; ok } }
  requireTip { "isaplanner/prop_27" in { prop_27; ok } }
  requireTip { "isaplanner/prop_28" in { prop_28; ok } }
  requireTip { "isaplanner/prop_29" in { prop_29; ok } }
  requireTip { "isaplanner/prop_30" in { prop_30; ok } }
  requireTip { "isaplanner/prop_31" in { prop_31; ok } }
  requireTip { "isaplanner/prop_32" in { prop_32; ok } }
  requireTip { "isaplanner/prop_33" in { prop_33; ok } }
  requireTip { "isaplanner/prop_34" in { prop_34; ok } }
  requireTip { "isaplanner/prop_35" in { prop_35; ok } }
  requireTip { "isaplanner/prop_36" in { prop_36; ok } }
  requireTip { "isaplanner/prop_37" in { prop_37; ok } }
  requireTip { "isaplanner/prop_38" in { prop_38; ok } }
  requireTip { "isaplanner/prop_39" in { prop_39; ok } }
  requireTip { "isaplanner/prop_40" in { prop_40; ok } }
  requireTip { "isaplanner/prop_41" in { prop_41; ok } }
  requireTip { "isaplanner/prop_42" in { prop_42; ok } }
  requireTip { "isaplanner/prop_43" in { prop_43; ok } }
  requireTip { "isaplanner/prop_44" in { prop_44; ok } }

  // prod
  requireTip { "prod/prop_01" in { at.logic.gapt.examples.tip.prod.prop_01; ok } }
  requireTip { "prod/prop_04" in { at.logic.gapt.examples.tip.prod.prop_04; ok } }
  requireTip { "prod/prop_05" in { at.logic.gapt.examples.tip.prod.prop_05; ok } }
  requireTip { "prod/prop_06" in { at.logic.gapt.examples.tip.prod.prop_06; ok } }
  requireTip { "prod/prop_07" in { at.logic.gapt.examples.tip.prod.prop_07; ok } }
  requireTip { "prod/prop_13" in { at.logic.gapt.examples.tip.prod.prop_13; ok } }
  requireTip { "prod/prop_15" in { at.logic.gapt.examples.tip.prod.prop_15; ok } }
  requireTip { "prod/prop_32" in { at.logic.gapt.examples.tip.prod.prop_32; ok } }
}
