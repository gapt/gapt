package gapt.provers.slakje

import gapt.expr._
import org.specs2.mutable.Specification

class SlakjeTest extends Specification {

  "lem" in { Slakje.getLKProof_( hos":- p | ~p" ) must_== Some( Left( () ) ) }
  "dne lem" in { Slakje.getLKProof_( hos":- ~ ~(p | ~p)" ) must beLike { case Some( Right( _ ) ) => ok } }
  "linear" in {
    Slakje.getLKProof_( hos"!x P(x,0), !x!y (!z P(f(x,z),y) -> P(x,s(y))) :- !x P(x,s(s(s(0))))" ) must beLike {
      case Some( Right( _ ) ) => ok
    }
  }

}
