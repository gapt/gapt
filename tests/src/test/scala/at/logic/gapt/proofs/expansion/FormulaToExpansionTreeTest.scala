package at.logic.gapt.proofs.expansion
import at.logic.gapt.expr._
import org.specs2.mutable.Specification

class FormulaToExpansionTreeTest extends Specification {

  "substituting bound variables" in {
    formulaToExpansionTree(
      hof"!x x=x",
      Set( Substitution( hov"x" -> le"x" ) ),
      Polarity.InAntecedent ).deep must_== hof"x=x"
  }

  "renamed bound variables" in {
    formulaToExpansionTree(
      hof"!x!y p x y",
      Set( Substitution( hov"x" -> le"y", hov"y" -> le"x" ) ),
      Polarity.InAntecedent ).deep must_== hof"p y x"
  }

}
