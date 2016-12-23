package at.logic.gapt.examples

import at.logic.gapt.examples.tip.isaplanner._
import at.logic.gapt.examples.tip.grammars._
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
  requireTip { "simp_expr_unambig1" in { simp_expr_unambig1; ok } }

  // isaplanner
  "isaplanner06" in { isaplanner06; ok }

  requireTip { "isaplanner07" in { isaplanner07; ok } }
  requireTip { "isaplanner08" in { isaplanner08; ok } }
  requireTip { "isaplanner09" in { isaplanner09; ok } }
  requireTip { "isaplanner10" in { isaplanner10; ok } }
  requireTip { "isaplanner11" in { isaplanner11; ok } }
  requireTip { "isaplanner12" in { isaplanner12; ok } }
  requireTip { "isaplanner13" in { isaplanner13; ok } }
  requireTip { "isaplanner14" in { isaplanner14; ok } }
  requireTip { "isaplanner15" in { isaplanner15; ok } }
  requireTip { "isaplanner16" in { isaplanner16; ok } }
  requireTip { "isaplanner17" in { isaplanner17; ok } }
  requireTip { "isaplanner18" in { isaplanner18; ok } }
  requireTip { "isaplanner19" in { isaplanner19; ok } }

  requireTip { "isaplanner21" in { isaplanner21; ok } }
  requireTip { "isaplanner22" in { isaplanner22; ok } }
  requireTip { "isaplanner23" in { isaplanner23; ok } }
  requireTip { "isaplanner24" in { isaplanner24; ok } }

  requireTip { "isaplanner26" in { isaplanner26; ok } }
  requireTip { "isaplanner27" in { isaplanner27; ok } }
  requireTip { "isaplanner28" in { isaplanner28; ok } }
  requireTip { "isaplanner29" in { isaplanner29; ok } }
  requireTip { "isaplanner30" in { isaplanner30; ok } }
  requireTip { "isaplanner31" in { isaplanner31; ok } }
  requireTip { "isaplanner32" in { isaplanner32; ok } }
  requireTip { "isaplanner33" in { isaplanner33; ok } }
  requireTip { "isaplanner34" in { isaplanner34; ok } }
  requireTip { "isaplanner35" in { isaplanner35; ok } }
  requireTip { "isaplanner36" in { isaplanner36; ok } }
  requireTip { "isaplanner37" in { isaplanner37; ok } }
  requireTip { "isaplanner38" in { isaplanner38; ok } }
  requireTip { "isaplanner39" in { isaplanner39; ok } }
  requireTip { "isaplanner40" in { isaplanner40; ok } }
  requireTip { "isaplanner41" in { isaplanner41; ok } }
  requireTip { "isaplanner42" in { isaplanner42; ok } }
  requireTip { "isaplanner43" in { isaplanner43; ok } }
  requireTip { "isaplanner44" in { isaplanner44; ok } }
}
