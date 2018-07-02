package gapt.examples

import gapt.examples.tip.grammars._
import gapt.examples.tip.isaplanner._
import gapt.provers.maxsat.OpenWBO
import org.specs2.mutable.Specification

class TipProofsTests extends Specification {

  // grammars
  "grammars/simp_expr_unambig1" in { simp_expr_unambig1; ok }

  // isaplanner
  "isaplanner/prop_03" in { prop_03; ok }
  "isaplanner/prop_06" in { prop_06; ok }

  "isaplanner/prop_07" in { prop_07; ok }
  "isaplanner/prop_08" in { prop_08; ok }
  "isaplanner/prop_09" in { prop_09; ok }
  "isaplanner/prop_10" in { prop_10; ok }
  "isaplanner/prop_11" in { prop_11; ok }
  "isaplanner/prop_12" in { prop_12; ok }
  "isaplanner/prop_13" in { prop_13; ok }
  "isaplanner/prop_14" in { prop_14; ok }
  "isaplanner/prop_15" in { prop_15; ok }
  "isaplanner/prop_16" in { prop_16; ok }
  "isaplanner/prop_17" in { prop_17; ok }
  "isaplanner/prop_18" in { prop_18; ok }
  "isaplanner/prop_19" in { prop_19; ok }

  "isaplanner/prop_21" in { prop_21; ok }
  "isaplanner/prop_22" in { prop_22; ok }
  "isaplanner/prop_23" in { prop_23; ok }
  "isaplanner/prop_24" in { prop_24; ok }

  "isaplanner/prop_26" in { prop_26; ok }
  "isaplanner/prop_27" in { prop_27; ok }
  "isaplanner/prop_28" in { prop_28; ok }
  "isaplanner/prop_29" in { prop_29; ok }
  "isaplanner/prop_30" in { prop_30; ok }
  "isaplanner/prop_31" in { prop_31; ok }
  "isaplanner/prop_32" in { prop_32; ok }
  "isaplanner/prop_33" in { prop_33; ok }
  "isaplanner/prop_34" in { prop_34; ok }
  "isaplanner/prop_35" in { prop_35; ok }
  "isaplanner/prop_36" in { prop_36; ok }
  "isaplanner/prop_37" in { prop_37; ok }
  "isaplanner/prop_38" in { prop_38; ok }
  "isaplanner/prop_39" in { prop_39; ok }
  "isaplanner/prop_40" in { prop_40; ok }
  "isaplanner/prop_41" in { prop_41; ok }
  "isaplanner/prop_42" in { prop_42; ok }
  "isaplanner/prop_43" in { prop_43; ok }
  "isaplanner/prop_44" in { prop_44; ok }
  "isaplanner/prop_45" in { prop_45; ok }
  "isaplanner/prop_46" in { prop_46; ok }
  "isaplanner/prop_47" in { prop_47; ok }
  "isaplanner/prop_48" in { prop_48; ok }
  "isaplanner/prop_49" in { prop_49; ok }

  // prod
  "prod/prop_01" in { gapt.examples.tip.prod.prop_01; ok }
  "prod/prop_04" in { gapt.examples.tip.prod.prop_04; ok }
  "prod/prop_05" in { gapt.examples.tip.prod.prop_05; ok }
  "prod/prop_06" in { gapt.examples.tip.prod.prop_06; ok }
  "prod/prop_07" in { gapt.examples.tip.prod.prop_07; ok }
  "prod/prop_08" in { gapt.examples.tip.prod.prop_08; ok }
  "prod/prop_10" in { gapt.examples.tip.prod.prop_10; ok }
  "prod/prop_13" in { gapt.examples.tip.prod.prop_13; ok }
  "prod/prop_15" in { gapt.examples.tip.prod.prop_15; ok }
  "prod/prop_16" in { gapt.examples.tip.prod.prop_16; ok }
  "prod/prop_20" in { gapt.examples.tip.prod.prop_20; ok }
  "prod/prop_27" in { gapt.examples.tip.prod.prop_27; ok }
  "prod/prop_28" in { gapt.examples.tip.prod.prop_28; ok }
  "prod/prop_29" in { gapt.examples.tip.prod.prop_29; ok }
  "prod/prop_30" in { gapt.examples.tip.prod.prop_30; ok }
  "prod/prop_31" in { if ( !OpenWBO.isInstalled ) skipped( "no openwbo" ); gapt.examples.tip.prod.prop_31; ok }
  "prod/prop_32" in { gapt.examples.tip.prod.prop_32; ok }
  "prod/prop_33" in { gapt.examples.tip.prod.prop_33; ok }
  "prod/prop_34" in { gapt.examples.tip.prod.prop_34; ok }
  "prod/prop_35" in { gapt.examples.tip.prod.prop_35; ok }
}
