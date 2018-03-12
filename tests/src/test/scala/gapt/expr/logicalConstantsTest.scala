package gapt.expr
import org.specs2.mutable._

class LogicalConstantsTest extends Specification {
  "Quantifiers" should {
    "have correct type" in {
      ForallC( Ti ->: To ).ty must_== ( ( ( Ti ->: To ) ->: To ) ->: To )
      ExistsC( Ti ->: To ).ty must_== ( ( ( Ti ->: To ) ->: To ) ->: To )
    }

    "match themselves" in {
      ForallC( Ti ) must beLike {
        case ExistsC( _ )  => ko
        case ForallC( Ti ) => ok
      }

      ExistsC( TBase( "foo" ) ) must beLike {
        case ForallC( _ )                   => ko
        case ExistsC( TBase( "foo", Nil ) ) => ok
      }
    }
  }

  "Propositional connectives" should {
    "have correct type" in {
      AndC().ty must_== ( To ->: To ->: To )
      OrC().ty must_== ( To ->: To ->: To )
      ImpC().ty must_== ( To ->: To ->: To )

      NegC().ty must_== ( To ->: To )

      TopC().ty must_== To
      BottomC().ty must_== To
    }

    "match themselves" in {
      AndC() must beLike {
        case OrC() | ImpC() | NegC() | TopC() | BottomC() => ko
        case AndC()                                       => ok
      }
      OrC() must beLike {
        case AndC() | ImpC() | NegC() | TopC() | BottomC() => ko
        case OrC()                                         => ok
      }
    }
  }

  "Equality" should {
    "have correct type" in {
      EqC( Ti ).ty must_== ( Ti ->: Ti ->: To )
      EqC( Ti ->: To ).ty must_== ( ( Ti ->: To ) ->: ( Ti ->: To ) ->: To )
    }
    "match itself" in {
      EqC( Ti ) must beLike { case EqC( Ti ) => ok }
    }
  }
}