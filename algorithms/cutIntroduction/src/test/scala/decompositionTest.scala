/*
 * Tests for computing the decomposition of terms
 *
 */

package at.logic.algorithms.cutIntroduction

import org.specs._
import org.specs.runner._
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.fol._
import termsExtraction._
import decomposition._

class decompositionTest extends SpecificationWithJUnit {

// On the comments of the examples below, consider A as alpha

  "The decomposition" should {
    "compute the delta-vector correctly" in {
      "initial example" in {
        // f(hggc, ggc), f(hgc, gc) --> (f(hgA, gA), {gc, c})

        val f = ConstantStringSymbol("f")
        val h = ConstantStringSymbol("h")
        val g = ConstantStringSymbol("g")
        val c = FOLConst(new ConstantStringSymbol("c"))
      
        val gc = Function(g, c::Nil)
        val ggc = Function( g, (Function(g, c::Nil))::Nil )
        val hgc = Function( h, (Function(g, c::Nil))::Nil )
        val hggc = Function(h, (Function(g, (Function(g, c::Nil))::Nil))::Nil)
      
        val f1 = Function(f, hggc::ggc::Nil)
        val f2 = Function(f, hgc::gc::Nil)
      
        val alpha = FOLVar(new VariableStringSymbol("alpha"))
        val galpha = Function(g, alpha::Nil)
        val hgalpha = Function(h, galpha::Nil)
        val common = Function(f, hgalpha::galpha::Nil)
      
        val dec = delta(f1::f2::Nil)
      
        (dec) must beEqual (common, gc::c::Nil)
      }

      "trivial decomposition" in {
        // f(hggc, gga), f(hgc, gb) --> (A, {f(hggc, gga), f(hgc, gb)})

        val f = ConstantStringSymbol("f")
        val h = ConstantStringSymbol("h")
        val g = ConstantStringSymbol("g")
        val c = FOLConst(new ConstantStringSymbol("c"))
        val b = FOLConst(new ConstantStringSymbol("b"))
        val a = FOLConst(new ConstantStringSymbol("a"))
      
        val gb = Function(g, b::Nil)
        val gga = Function( g, (Function(g, a::Nil))::Nil )
        val hgc = Function( h, (Function(g, c::Nil))::Nil )
        val hggc = Function(h, (Function(g, (Function(g, c::Nil))::Nil))::Nil)
      
        val f1 = Function(f, hggc::gga::Nil)
        val f2 = Function(f, hgc::gb::Nil)
      
        val alpha = FOLVar(new VariableStringSymbol("alpha"))
      
        val dec = delta(f1::f2::Nil)
      
        (dec) must beEqual (alpha, f1::f2::Nil)
 
      }

      "decomposition with neutral element" in {
        // f(hggc, ga), f(hgc, ga) --> (f(hgA, ga), {gc, c})

        val f = ConstantStringSymbol("f")
        val h = ConstantStringSymbol("h")
        val g = ConstantStringSymbol("g")
        val c = FOLConst(new ConstantStringSymbol("c"))
        val a = FOLConst(new ConstantStringSymbol("a"))
      
        val ga = Function(g, a::Nil)
        val gc = Function(g, c::Nil)
        val hgc = Function( h, (Function(g, c::Nil))::Nil )
        val hggc = Function(h, (Function(g, (Function(g, c::Nil))::Nil))::Nil)
      
        val f1 = Function(f, hggc::ga::Nil)
        val f2 = Function(f, hgc::ga::Nil)
      
        val alpha = FOLVar(new VariableStringSymbol("alpha"))
        val galpha = Function(g, alpha::Nil)
        val hgalpha = Function(h, galpha::Nil)
        val common = Function(f, hgalpha::ga::Nil)
      
        val dec = delta(f1::f2::Nil)
      
        (dec) must beEqual (common, gc::c::Nil)
 
      }
    }
  }
}
