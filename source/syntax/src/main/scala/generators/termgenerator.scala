/* Generator for First Order Terms
 * function symbols with the same name but different arity will not be constructed */

package at.logic.utils.generators

import scala.util.Random
import at.logic.language.fol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._

class FOLtermGenerator {
    var random : Random = null
    var count = 0 // every generated variable, constant symbol

    def apply(seed : Int) = new FOLtermGenerator(seed)

    def this(seed : Int) = {
        this()
        random = new Random(seed);
    }


    def generateVariable() = {
        count += 1
        var x = new VariableStringSymbol("x_"+count) ;
        FOLFactory.createVar(x, i)
    }
    
}