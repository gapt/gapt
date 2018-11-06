package gapt.cutintro

import gapt.expr._
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.gaptic._
import gapt.proofs.lk.CutRule
import gapt.provers.maxsat.OpenWBO
import org.specs2.mutable.Specification

class Pi2CutIntroTest extends Specification {

  "totality example" in {
    if ( !OpenWBO.isInstalled ) skipped

    implicit val ctx = MutableContext.default()
    ctx += Ti
    ctx += hoc"P:i>i>o"
    ctx += hoc"f:i>i"
    ctx += hoc"g:i>i"
    ctx += hoc"h:i>i"
    ctx += hoc"i:i>i"
    ctx += hoc"c:i"

    val p = Lemma( hols"h: !x (P x (f x) | P x (g x) | P x (h x) | P x (i x)) :- ?x?y?z (P x y & P y z)" ) {
      cut( "c", hof"!x?y P x y" ) left by { forget( "g" ); escrgt }
      forget( "h" ); escrgt
    }

    // FIXME: this text is so flaky, it might as well be flipping coins
    // It depends on at least: expression hash code and the name of the implication constant
    // If it doesn't work try random mutations in the variable names below...
    Pi2CutIntroduction( p, fov"xa", Vector( fov"b1", fov"b2" ) ) must beLike {
      case Some( q ) =>
        val Some( cut ) = q.subProofs.find( _.isInstanceOf[CutRule] )
        ok
    }

  }

}
