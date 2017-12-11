package at.logic.gapt.cutintro

import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Context, MutableContext }
import at.logic.gapt.proofs.lk.CutRule
import at.logic.gapt.provers.maxsat.OpenWBO
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
    ctx += hoc"c:i"

    val p = Lemma( hols"h: !x (P x (f x) | P x (g x) | P x (h x)) :- ?x?y?z?w (P x y & P y z & P z w)" ) {
      cut( "c", hof"!x?y P x y" )

      forget( "g" ); decompose
      allL( "h", le"x" ).forget
      destruct( "h" )
      destruct( "h" )
      exR( le"f x" ); prop
      exR( le"g x" ); prop
      exR( le"h x" ); prop

      forget( "h" )
      allL( le"c" ); decompose
      allL( le"y" ); decompose
      allL( le"y_0" ); decompose
      exR( le"c", le"y", le"y_0", le"y_1" ).forget
      prop
    }

    Pi2CutIntroduction( p, fov"xa", Vector( fov"xb1", fov"xb2", fov"xb3" ) ) must beLike {
      case Some( q ) =>
        val Some( cut ) = q.subProofs.find( _.isInstanceOf[CutRule] )
        ok
    }

  }

}
