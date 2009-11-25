/* Generator for First Order Terms
 * function symbols with the same name but different arity will not be constructed */

package at.logic.utils.generators

import scala.util.Random
import at.logic.language.fol._

class FOLtermGenerator {
    var random : Random = null

    def apply(seed : Int) = new FOLtermGenerator(seed)

    //def this() = {}
    def this(seed : Int) = {
        this()
        random = new Random(seed);
    }


    def generateVariable() {}
    
}