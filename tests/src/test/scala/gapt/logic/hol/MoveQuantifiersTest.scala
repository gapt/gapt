package gapt.logic.hol

import gapt.expr._
import gapt.expr.formula.constants.QuantifierC
import gapt.expr.formula.{ All, Ex, Formula, Or, QuantifierHelper }
import org.specs2.mutable.Specification
import org.specs2.specification.core.Fragment

class MoveQuantifiersTest extends Specification {
  def testWithMessage(
    quantifier:      QuantifierHelper,
    formula:         Formula,
    expectedFormula: Formula,
    testFunction:    ( QuantifierHelper, Formula ) => Formula,
    message:         ( QuantifierHelper, Formula, Formula ) => String ): Fragment = {
    message( quantifier, formula, expectedFormula ) in {
      testFunction( quantifier, formula ) must beEqualTo( expectedFormula )
    }
  }

  "moveQuantifiers.up" should {
    def succeedFor = testWithMessage( _, _, _, moveQuantifiers.up, {
      case ( quantifier, formula, expectedFormula ) => s"move '${quantifier.q.name}' up in $formula to get $expectedFormula"
    } )

    def notMove( quantifier: QuantifierHelper, formula: Formula ) =
      testWithMessage( quantifier, formula, formula, moveQuantifiers.up, {
        case ( quantifier, formula, _ ) => s"not move '$quantifier' up in $formula"
      } )

    notMove( Ex, hof"R(a)" )
    succeedFor( All, hof"!x x=a & !x x=b", hof"!x (x=a & x=b)" )
    succeedFor( Ex, hof"?x x=a | ?x x=b", hof"?x (x=a | x=b)" )
    succeedFor( All, hof"(!x x=a) & R(b)", hof"!x (x=a & R(b))" )
    succeedFor( All, hof"(!x R(x)) | R(b)", hof"!x (R(x) | R(b))" )
    succeedFor( All, hof"?x (R(x, b) & !y R(x, y))", hof"?x !y (R(x, b) & R(x, y))" )
    succeedFor( Ex, hof"?x !u ((?w !y R(y, w)) & ?z S(z, x))", hof"?x !u ?w ?z ((!y R(y, w)) & S(z, x))" )
    succeedFor( Ex, hof"(?x ((?y R(y)) & R(x))) | (?x S(x))", hof"?x ?y ((R(y) & R(x)) | S(x))" )
    succeedFor( All, hof"-((!x R(x)) & (!x S(x)))", hof"-(!x (R(x) & S(x)))" )

    val q = new QuantifierHelper( new QuantifierC( "q" ) )
    notMove( q, q( fov"x", hof"R(x) | S(x)" ) )
  }

  "moveQuantifiers.down" should {
    def succeedFor( quantifier: QuantifierHelper, formula: Formula, expectedFormula: Formula ): Fragment =
      testWithMessage( quantifier, formula, expectedFormula, moveQuantifiers.down, {
        case ( quantifier, formula, expectedFormula ) => s"move '${quantifier.q.name}' down in $formula to get $expectedFormula"
      } )

    def notMove( quantifier: QuantifierHelper, formula: Formula ): Fragment =
      testWithMessage( quantifier, formula, formula, moveQuantifiers.down, {
        case ( quantifier, formula, _ ) => s"not move '${quantifier.q.name}' down in $formula"
      } )

    notMove( All, hof"R(a)" )
    notMove( Ex, hof"R(a) & R(b)" )
    notMove( All, hof"?x R(x)" )
    succeedFor( Ex, hof"?x (R(x) & R(b))", hof"(?x R(x)) & R(b)" )
    succeedFor( All, hof"!x (R(a) | R(x))", hof"R(a) | (!x R(x))" )
    succeedFor( Ex, hof"?x (R(x) | S(x))", hof"(?x R(x)) | (?x S(x))" )
    notMove( All, hof"!x (R(x) | S(x))" )
    notMove( All, hof"!x ?y !z R(x, y, z)" )
    succeedFor( All, hof"-(!x (R(x) & S(x)))", hof"-((!x R(x)) & (!x S(x)))" )

    val q = new QuantifierHelper( new QuantifierC( "q" ) )
    notMove( q, q( fov"x", hof"R(x) | S(x)" ) )
    succeedFor( q, q( fov"x", hof"R(x) | S(a)" ), Or( q( fov"x", hof"R(x)" ), hof"S(a)" ) )
  }
}