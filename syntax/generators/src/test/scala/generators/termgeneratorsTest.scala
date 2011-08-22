/* Test cases for the term generator.
*/

package at.logic.utils.generators

import scala.util.Random
import at.logic.language.fol._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.hol.logicSymbols._

import org.specs._
import org.specs.runner._
import org.scalacheck._
import org.scalacheck.Prop._

import org.specs.matcher._

import at.logic.utils.testing.PropMatcher.bePassed

class termgeneratorTest extends SpecificationWithJUnit {
    "The generator" should {
        "be able to convert between tuples and langauges" in {
            //import Language.languageFromTuple
            //import Language.tupleFromLanguage

            val prop = forAll( (seed:Int, nv0:Int, nc0:Int, nf0:Int) => {
              val nv = nv0 % 100
              val nc = nc0 % 100
              val nf = nf0 % 100

                var generator = new FOLtermGenerator(seed)
                val s  : (List[(VariableSymbolA,Int)], List[(ConstantSymbolA,Int)],List[(ConstantSymbolA,Int)]) = generator.generateSymbols(nv,nc,nf,7)
                val l  : Language = s
                val s2 : (List[(VariableSymbolA,Int)], List[(ConstantSymbolA,Int)],List[(ConstantSymbolA,Int)]) = l
                val l2 : Language = s2
                s == s2 && l == l2
            })

            prop must bePassed
        }

        val seed = 123
        "generate languages of a given size" in {
            var generator = new FOLtermGenerator(seed)
            var prop = forAll( (nv0:Int, nc0:Int, nf0:Int) => {
              val nv = nv0 % 100
              val nc = nc0 % 100
              val nf = nf0 % 100
                    var v = if (nv<0) 0 else nv
                    var c = if (nc<0) 0 else nc
                    var f = if (nf<0) 0 else nf

                    generator.generateSymbols(v,c,f,7) match {
                        case (vs,cs,fs) => //println((v,c,f)); println((vs,cs,fs));
                                           vs.length == v &&
                                           cs.length == c &&
                                           fs.length == f
                    }
                })
            prop must bePassed
        }

        "generate languages of a given size from random strings" in {
            var generator = new FOLtermGenerator(seed)
            var prop = forAll( (vs:List[String],cs:List[String],fs:List[String]) => {
                    val l:Language = Language.tupleFromStrings((vs,cs,fs))
                        l match {
                            case Language(v,c,f) => v.length == vs.length &&
                                                    c.length == cs.length &&
                                                    f.length == fs.length
                        }
                })
            prop must bePassed
        }

      /*
        "generate first order variables" in {
            var generator = new FOLtermGenerator(seed)
            val l = generator.generateSymbols(10,5,6,5)
            generator.generateVariable(l) match {
                case x:FOLVar =>
                    x.name.toString must be matching ("x_[0-9]+")
                    x.exptype  must beEqual (i)
                case _ => true must beEqual (false)
            }


        }*/

        "generate first order functions" in {
            //symbol names must be in the language
            val prop : Prop = forAll( (seed : Int) => {
                   //println("!!seed="+seed)
                var generator = new FOLtermGenerator(seed)
                val l = generator.generateSymbols(10,5,6,5)
                val x = generator.generateFunction(l, 30, 50, 7)
                val symbols : List[String] = (l._1 ++ l._2 ++ l._3).map( (x=>x._1.toString) )
                val getName : (FOLTerm=>String) = ((t:FOLTerm)=>{t match {
                            case FOLVar(x)     => x.toString
                            case FOLConst(x)   => x.toString
                            case Function(x,y) => x.toString
                            case _=> ""
                    }})
                val fun = ((ft:FOLTerm)=> { symbols.contains(getName(ft))} )
                val conj = ((b1:Boolean,b2:Boolean)=> {b1 && b2})
                val tests = Language.flattenTerm(x).map(fun)
                //println(symbols)
                Language.printTerm(x)
                //println(Language.flattenTerm(x).map(getName))
                //println(tests)
                val r : Boolean = tests.foldLeft(true)(conj)
                r
                
                })
            //prop.desc = td
            //Test.Params
            prop must bePassed

        }
    }
}