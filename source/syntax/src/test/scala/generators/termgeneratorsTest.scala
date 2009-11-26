/* Test cases for the term generator.
*/

package at.logic.utils.generators

import scala.util.Random
import at.logic.language.fol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._

import org.specs._
import org.specs.runner._
import org.scalacheck._
import org.scalacheck.Prop._

import org.specs.matcher._

import at.logic.utils.testing.PropMatcher.bePassed

class termgeneratorTest extends SpecificationWithJUnit {
    "The generator " should {
        val seed = 123
        "be able to convert between tuples and langauges" in {
            import Language.tupleFromLanguage
            import Language.languageFromTuple
            var generator = new FOLtermGenerator(seed)

            val prop = forAll( (nv:Int, nc:Int, nf:Int) => {
                val s  : (List[SymbolA], List[SymbolA], List[SymbolA]) = generator.generateSymbols(nv,nv,nf)
                val l  : Language = s
                val s2 : (List[SymbolA], List[SymbolA], List[SymbolA]) = l
                val l2 : Language = s2
                s == s2 && l == l2
            })

            prop must bePassed
        }

        "generate languages of a given size" in {
            var generator = new FOLtermGenerator(seed)
            var prop = forAll( (nv:Int, nc:Int, nf:Int) => {
                    var v = if (nv<0) 0 else nv
                    var c = if (nc<0) 0 else nc
                    var f = if (nf<0) 0 else nf

                    generator.generateSymbols(v,c,f) match {
                        case (vs,cs,fs) => //println((v,c,f)); println((vs,cs,fs));
                                           vs.length == v &&
                                           cs.length == c &&
                                           fs.length == f
                    }
                })
            prop must bePassed
        }

        "generate first order variables" in {
            var generator = new FOLtermGenerator(seed)
            generator.generateVariable match {
                case x:FOLVar => 
                    x.name must beEqual (new VariableStringSymbol("x_1"))
                    x.exptype  must beEqual (i)
                case _ => true must beEqual (false)
            }
            
        }
    }
}