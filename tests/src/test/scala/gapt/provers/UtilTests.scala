package gapt.provers

import org.specs2.mutable.Specification

class UtilTests extends Specification {

  "name mangling should get rid of some greek letters" in {
    val greekLetters = List("α", "β", "γ", "ν")
    foreach(greekLetters.map(mangleName(_))) { mangledName =>
      foreach(greekLetters) { letter => mangledName must not contain (letter) }
    }
  }

  "name mangling should get rid of operators" in {
    val operators = List("+", "*", "-", "/")
    foreach(operators.map(mangleName(_))) { mangledName =>
      foreach(operators) { operator => mangledName must not contain (operator) }
    }
  }

}
