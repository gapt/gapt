package gapt.provers.escargot

import gapt.expr._
import org.specs2.mutable.Specification

class EscargotChaudTest extends Specification {

  "1" in {
    val clauses = Seq(
      hcl"P x :- P y" -> false,
      hcl"x=y, P x :- P y" -> true,
      hcl"P x :- x=x" -> true,
      hcl"Q x, y=x :- Q y" -> true,
      hcl"Qx :- Qy" -> false )

    val chaud = new EscargotChaud( clauses.flatMap( _._1.elements ) )

    for ( ( c, isValid ) <- clauses ) {
      val p = chaud.getAtomicLKProof( c )
      if ( isValid )
        p must beSome
      else
        p must beNone
    }

    ok
  }

}
