package gapt.expr.schema

import gapt.expr._
import gapt.expr.ty._
import org.specs2.mutable._

class NumeralTest extends Specification {

  // Numeral tests
  "Schematic Numerals" should {
    "create a numeral for the number 5" in {
      Numeral(5) match {
        case Succ(Succ(Succ(Succ(Succ(Zero))))) => ok
        case _ => ko
      }
    }

     "create a numeral for the number 0" in {
      Numeral(0) match {
        case Zero => ok
        case _ => ko
      }
    }

    "evaluate the numeral 5 to the number 5" in {
      Succ(Succ(Succ(Succ(Succ(Zero))))) match {
        case Numeral(5) => ok
        case _ => ko
      }
    }
    "evaluate the numeral 0 to the number 0" in {
      Zero match {
        case Numeral(0) => ok
        case _ => ko
      }
    }
    "throw an exception for the number -1" in {
      Numeral(-1) must throwA(new IllegalArgumentException(s"Negative number s{n} does not have a numeral associated!"))
    }


  


  // Normalize tests
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

  "normalize p(p(s(s(x)))) to x" in {
    val x = Var("x", Tw)
    val numeral = Pred(Pred(Succ(Succ(x))))
    Normalize(numeral) match {
      case n if n == x => ok
      case _ => ko
    }
  }

  "normalize p(s(s(x))) to S(x)" in {
    val x = Var("x", Tw)
    val numeral = Pred(Succ(Succ(x)))
    Normalize(numeral) match {
      case n if n == Succ(x) => ok
      case _ => ko
    }
  }

  "normalize s(p(s(x))) to S(x)" in {
    val x = Var("x", Tw)
    val numeral = Succ(Pred(Succ(x)))
    Normalize(numeral) match {
      case n if n == Succ(x) => ok
      case _ => ko
    }
  }

  "throw an exception for Const('b', To, Nil) " in {
      val b = Const("b", To, Nil)
      Normalize(b) must throwA(new IllegalArgumentException("Argument must be of type ω!"))
      
    }



// Convert tests
  "should convert the Numeral(5) to integer 5" in {
      Numeral.convert(Numeral(5)) match {
        case 5 => ok
        case _ => ko
      }
    }

  "should convert Succ(Pred(Succ(Zero))) to integer 1" in {
      Numeral.convert(Succ(Pred(Succ(Zero)))) match {
        case 1 => ok
        case _ => ko
      }
    }

  "should convert Pred(Pred(Succ(Succ(Zero)))) to integer 0" in {
      Numeral.convert(Pred(Pred(Succ(Succ(Zero))))) match {
        case 0 => ok
        case _ => ko
      }
    }

  "should convert Pred(Pred(Succ(Succ(Zero)))) to integer 0" in {
      Numeral.convert(Pred(Pred(Succ(Succ(Zero))))) match {
        case 0 => ok
        case _ => ko
      }
    }

  "throw an exception for Const('b', To, Nil) " in {
        val b = Const("b", To, Nil)
        Numeral.convert(b) must throwA(new IllegalArgumentException(s"Expression ${b} is not a numeral!"))
        
      }


}

}