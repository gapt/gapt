/*
 * Tests for computing the decomposition of terms
 *
 */

package at.logic.algorithms.cutIntroduction

import org.specs._
import org.specs.runner._
import scala.collection.mutable.HashMap
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

      "terms from the paper example (more than 2 terms)" in {
        // fa, f²a, f³a --> (fA, {a, fa, f²a})
        
        val f = ConstantStringSymbol("f")
        val a = FOLConst(new ConstantStringSymbol("a"))

        val fa = Function(f, a::Nil)
        val f2a = Function(f, (Function(f, a::Nil))::Nil)
        val f3a = Function(f, (Function(f, (Function(f, a::Nil))::Nil))::Nil)
        
        val alpha = FOLVar(new VariableStringSymbol("alpha"))
        val falpha = Function(f, alpha::Nil)

        val dec = delta(fa::f2a::f3a::Nil)

        (dec) must beEqual (falpha, a::fa::f2a::Nil)
      }
    }

    "compute the delta-table correctly" in {
      "for the f^i(a) set of terms (i = 1 to 4)" in {
        // fa, f²a, f³a, f⁴a

        val f = ConstantStringSymbol("f")
        val a = FOLConst(new ConstantStringSymbol("a"))
        
        val fa = Function(f, a::Nil)
        val f2a = Function(f, (Function(f, a::Nil))::Nil)
        val f3a = Function(f, (Function(f, (Function(f, a::Nil))::Nil))::Nil)
        val f4a = Function(f, (Function(f, (Function(f, (Function(f, a::Nil))::Nil))::Nil))::Nil)

        val alpha = FOLVar(new VariableStringSymbol("alpha"))
        val falpha = Function(f, alpha::Nil)
        val f2alpha = Function(f, (Function(f, alpha::Nil))::Nil)
        val f3alpha = Function(f, (Function(f, (Function(f, alpha::Nil))::Nil))::Nil)

        val expected = new HashMap[List[FOLTerm], List[(FOLTerm, List[FOLTerm])]]
        expected += ( (fa::Nil) -> ((alpha, fa::Nil)::Nil) )
        expected += ( (f2a::Nil) -> ((alpha, f2a::Nil)::Nil) )
        expected += ( (f3a::Nil) -> ((alpha, f3a::Nil)::Nil) )
        expected += ( (f4a::Nil) -> ((alpha, f4a::Nil)::Nil) )
        expected += ( (a::fa::Nil) -> ((f2alpha, f2a::f3a::Nil)::(f3alpha, f3a::f4a::Nil)::(falpha, fa::f2a::Nil)::Nil) )
        expected += ( (a::f2a::Nil) -> ((f2alpha, f2a::f4a::Nil)::(falpha, fa::f3a::Nil)::Nil) )
        expected += ( (a::f3a::Nil) -> ((falpha, fa::f4a::Nil)::Nil) )
        expected += ( (a::fa::f2a::Nil) -> ((f2alpha, f2a::f3a::f4a::Nil)::(falpha, fa::f2a::f3a::Nil)::Nil) )
        expected += ( (a::fa::f3a::Nil) -> ((falpha, fa::f2a::f4a::Nil)::Nil) ) 
        expected += ( (a::f2a::f3a::Nil) -> ((falpha, fa::f3a::f4a::Nil)::Nil) )
        expected += ( (a::fa::f2a::f3a::Nil) -> ((falpha, fa::f2a::f3a::f4a::Nil)::Nil) )

        val deltatable = computeDeltaTable(fa::f2a::f3a::f4a::Nil)

        // Note: if elements in the inner lists are not on the same order, 
        // this returns false.
        (deltatable) must haveTheSameElementsAs (expected)
      }
      
      "for Stefan's example" in {
        // t1 = f(c, gc)
        // t2 = f(c, g²c)
        // t3 = f(c, g³c)
        // t4 = f(gc, c)
        // t5 = f(g²c, gc)
        // t6 = f(g³c, g²c)

        val f = ConstantStringSymbol("f")
        val g = ConstantStringSymbol("g")
        val c = FOLConst(new ConstantStringSymbol("c"))

        val gc = Function(g, c::Nil)
        val g2c = Function(g, (Function(g, c::Nil))::Nil)
        val g3c = Function(g, (Function(g, (Function(g, c::Nil))::Nil))::Nil)
       
        val t1 = Function(f, c::gc::Nil)
        val t2 = Function(f, c::g2c::Nil)  
        val t3 = Function(f, c::g3c::Nil)
        val t4 = Function(f, gc::c::Nil)
        val t5 = Function(f, g2c::gc::Nil)
        val t6 = Function(f, g3c::g2c::Nil)

        val alpha = FOLVar(new VariableStringSymbol("alpha"))
        val galpha = Function(g, alpha::Nil)
        val g2alpha = Function(g, (Function(g, alpha::Nil))::Nil)
        val f_c_galpha = Function(f, c::galpha::Nil)
        val f_c_g2alpha = Function(f, c::g2alpha::Nil)
        val f_galpha_alpha = Function(f, galpha::alpha::Nil)
        val f_g2alpha_galpha = Function(f, g2alpha::galpha::Nil)
        val f_alpha_gc = Function(f, alpha::gc::Nil)
        val f_alpha_g2c = Function(f, alpha::g2c::Nil)
        
        val expected = new HashMap[List[FOLTerm], List[(FOLTerm, List[FOLTerm])]]
        expected += ( (t1::Nil) -> ((alpha, t1::Nil)::Nil) )
        expected += ( (t2::Nil) -> ((alpha, t2::Nil)::Nil) )
        expected += ( (t3::Nil) -> ((alpha, t3::Nil)::Nil) )
        expected += ( (t4::Nil) -> ((alpha, t4::Nil)::Nil) )
        expected += ( (t5::Nil) -> ((alpha, t5::Nil)::Nil) )
        expected += ( (t6::Nil) -> ((alpha, t6::Nil)::Nil) )
        expected += ( (c::gc::Nil) -> ((f_c_g2alpha, t2::t3::Nil)::(f_galpha_alpha, t4::t5::Nil)::(f_g2alpha_galpha, t5::t6::Nil)::(f_c_galpha, t1::t2::Nil)::Nil) )
        expected += ( (c::g2c::Nil) -> ((f_galpha_alpha, t4::t6::Nil)::(f_c_galpha, t1::t3::Nil)::(f_alpha_gc, t1::t5::Nil)::Nil) )
        expected += ( (c::g3c::Nil) -> ((f_alpha_g2c, t2::t6::Nil)::Nil) )
        expected += ( (c::gc::g2c::Nil) -> ((f_galpha_alpha, t4::t5::t6::Nil)::(f_c_galpha, t1::t2::t3::Nil)::Nil) )

        val deltatable = computeDeltaTable(t1::t2::t3::t4::t5::t6::Nil)

        // Note: if elements in the inner lists are not on the same order, 
        // this returns false.
        (deltatable) must haveTheSameElementsAs (expected)
      }
    }
/*
    "find the right decompositions for" in {
      "paper's example" in {

      }

      "Stefan's example" in {

      }
    }
*/
  }
}
