package at.logic.gapt.expr
import org.specs2.mutable._

class LogicalConstantsTest extends Specification {
  "Quantifiers" should {
    "have correct type" in {
      ForallC( Ti -> To ).exptype must_== ( ( ( Ti -> To ) -> To ) -> To )
      ExistsC( Ti -> To ).exptype must_== ( ( ( Ti -> To ) -> To ) -> To )
    }

    "match themselves" in {
      ForallC( Ti ) must beLike {
        case ExistsC( _ )  => ko
        case ForallC( Ti ) => ok
      }

      ExistsC( TBase( "foo" ) ) must beLike {
        case ForallC( _ )              => ko
        case ExistsC( TBase( "foo" ) ) => ok
      }
    }
  }

  "Propositional connectives" should {
    "have correct type" in {
      AndC().exptype must_== ( To -> ( To -> To ) )
      OrC().exptype must_== ( To -> ( To -> To ) )
      ImpC().exptype must_== ( To -> ( To -> To ) )

      NegC().exptype must_== ( To -> To )

      TopC().exptype must_== To
      BottomC().exptype must_== To
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
      EqC( Ti ).exptype must_== ( Ti -> ( Ti -> To ) )
      EqC( Ti -> To ).exptype must_== ( ( Ti -> To ) -> ( ( Ti -> To ) -> To ) )
    }
    "match itself" in {
      EqC( Ti ) must beLike { case EqC( Ti ) => ok }
    }
  }
}