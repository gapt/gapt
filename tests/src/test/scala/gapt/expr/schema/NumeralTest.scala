package gapt.expr.schema

import gapt.expr._
import org.specs2.mutable._

class NumeralTest extends Specification {
  "Schematic Numerals" should {
    "create a numeral for the number 5" in {
      Numeral(5) match {
        case Succ(Succ(Succ(Succ(Succ(Zero))))) => ok
        case _ => ko
      }
    }

    "evaluate the numeral 5 to the number 5" in {
      Succ(Succ(Succ(Succ(Succ(Zero))))) match {
        case Numeral(5) => ok
        case _ => ko
      }
    }
  }

  "normalize the numeral 5 to itself" in {
    Normalize(Numeral(5)) match {
      case Numeral(5) => ok
      case _ => ko
    }
  }

  "normalize s(p(s(p(x)))) to x" in {
    val x = Var("x", Tw)
    val numeral = Succ(Pred(Succ(Pred(x))))
    Normalize(numeral) match {
      case n if n == x => ok
      case _ => ko
    }
  }

  "normalize s(s(p(p(x)))) to x" in {
    val x = Var("x", Tw)
    val numeral = Succ(Succ(Pred(Pred(x))))
    Normalize(numeral) match {
      case n if n == x => ok
      case _ => ko
    }
  }

}
