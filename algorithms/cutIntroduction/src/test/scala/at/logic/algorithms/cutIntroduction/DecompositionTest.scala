/*
 * Tests for computing the decomposition of terms
 *
 */

package at.logic.algorithms.cutIntroduction

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import scala.collection.mutable.HashMap
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.fol._
import TermsExtraction._
import Decomposition._

@RunWith(classOf[JUnitRunner])
class DecompositionTest extends SpecificationWithJUnit {

// On the comments of the examples below, consider A as α

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
      
        val alpha = FOLVar(new VariableStringSymbol("α"))
        val galpha = Function(g, alpha::Nil)
        val hgalpha = Function(h, galpha::Nil)
        val common = Function(f, hgalpha::galpha::Nil)
      
        val dec = delta(f1::f2::Nil, alpha)
      
        (dec) must beEqualTo (common, gc::c::Nil)
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
      
        val alpha = FOLVar(new VariableStringSymbol("α"))
      
        val dec = delta(f1::f2::Nil, alpha)
      
        (dec) must beEqualTo (alpha, f1::f2::Nil)
 
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
      
        val alpha = FOLVar(new VariableStringSymbol("α"))
        val galpha = Function(g, alpha::Nil)
        val hgalpha = Function(h, galpha::Nil)
        val common = Function(f, hgalpha::ga::Nil)
      
        val dec = delta(f1::f2::Nil, alpha)
      
        (dec) must beEqualTo (common, gc::c::Nil)
 
      }

      "terms from the paper example (more than 2 terms)" in {
        // fa, f²a, f³a --> (fA, {a, fa, f²a})
        
        val f = ConstantStringSymbol("f")
        val a = FOLConst(new ConstantStringSymbol("a"))

        val fa = Function(f, a::Nil)
        val f2a = Function(f, (Function(f, a::Nil))::Nil)
        val f3a = Function(f, (Function(f, (Function(f, a::Nil))::Nil))::Nil)
        
        val alpha = FOLVar(new VariableStringSymbol("α"))
        val falpha = Function(f, alpha::Nil)

        val dec = delta(fa::f2a::f3a::Nil, alpha)

        (dec) must beEqualTo (falpha, a::fa::f2a::Nil)
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

        val alpha = FOLVar(new VariableStringSymbol("α"))
        val falpha = Function(f, alpha::Nil)
        val f2alpha = Function(f, (Function(f, alpha::Nil))::Nil)
        val f3alpha = Function(f, (Function(f, (Function(f, alpha::Nil))::Nil))::Nil)

        val expected = new HashMap[List[FOLTerm], List[(FOLTerm, List[FOLTerm])]]
        expected += ( (Nil) -> ((null, Nil)::Nil) )
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

        val deltatable = new DeltaTable(fa::f2a::f3a::f4a::Nil, alpha)

        // Note: if elements in the inner lists are not on the same order, 
        // this returns false.
        (deltatable.table) must haveTheSameElementsAs (expected)
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

        val alpha = FOLVar(new VariableStringSymbol("α"))
        val galpha = Function(g, alpha::Nil)
        val g2alpha = Function(g, (Function(g, alpha::Nil))::Nil)
        val f_c_galpha = Function(f, c::galpha::Nil)
        val f_c_g2alpha = Function(f, c::g2alpha::Nil)
        val f_galpha_alpha = Function(f, galpha::alpha::Nil)
        val f_g2alpha_galpha = Function(f, g2alpha::galpha::Nil)
        val f_alpha_gc = Function(f, alpha::gc::Nil)
        val f_alpha_g2c = Function(f, alpha::g2c::Nil)
        
        val expected = new HashMap[List[FOLTerm], List[(FOLTerm, List[FOLTerm])]]
        expected += ( (Nil) -> ((null, Nil)::Nil) )
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

        val deltatable = new DeltaTable(t1::t2::t3::t4::t5::t6::Nil, alpha)

        // Note: if elements in the inner lists are not on the same order, 
        // this returns false.
        (deltatable.table) must haveTheSameElementsAs (expected)
      }
    }

    "find the right decompositions for" in {
      "the paper's example" in {
        // fa, f²a, f³a, f⁴a

        val f = ConstantStringSymbol("f")
        val a = FOLConst(new ConstantStringSymbol("a"))
        
        val fa = Function(f, a::Nil)
        val f2a = Function(f, (Function(f, a::Nil))::Nil)
        val f3a = Function(f, (Function(f, (Function(f, a::Nil))::Nil))::Nil)
        val f4a = Function(f, (Function(f, (Function(f, (Function(f, a::Nil))::Nil))::Nil))::Nil)

        val alpha = FOLVar(new VariableStringSymbol("α"))
        val falpha = Function(f, alpha::Nil)
        val f2alpha = Function(f, (Function(f, alpha::Nil))::Nil)
        val f3alpha = Function(f, (Function(f, (Function(f, alpha::Nil))::Nil))::Nil)

        var expected : List[(List[FOLTerm], List[FOLTerm])] = Nil
        expected = expected :+ (f3alpha::falpha::Nil, a::fa::Nil)
        expected = expected :+ (f2alpha::f3alpha::falpha::Nil, a::fa::Nil)
        expected = expected :+ (f2alpha::falpha::Nil, a::f2a::Nil)
        expected = expected :+ (f2alpha::falpha::Nil, a::fa::f2a::Nil)
        expected = expected :+ (falpha::Nil, a::fa::f2a::f3a::Nil)

        val d = Decomposition(fa::f2a::f3a::f4a::Nil)

        (d) must haveTheSameElementsAs (expected)

      }

      "Stefan's example" in {
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

        val alpha = FOLVar(new VariableStringSymbol("α"))
        val galpha = Function(g, alpha::Nil)
        val g2alpha = Function(g, (Function(g, alpha::Nil))::Nil)
        val f_c_galpha = Function(f, c::galpha::Nil)
        val f_c_g2alpha = Function(f, c::g2alpha::Nil)
        val f_galpha_alpha = Function(f, galpha::alpha::Nil)
        val f_g2alpha_galpha = Function(f, g2alpha::galpha::Nil)
        val f_alpha_gc = Function(f, alpha::gc::Nil)
        val f_alpha_g2c = Function(f, alpha::g2c::Nil)
        
        var expected : List[(List[FOLTerm], List[FOLTerm])] = Nil
        expected = expected :+ (f_c_g2alpha::f_galpha_alpha::f_g2alpha_galpha::f_c_galpha::Nil, c::gc::Nil)
        expected = expected :+ (f_galpha_alpha::f_c_galpha::Nil, c::gc::g2c::Nil)

        val d = Decomposition(t1::t2::t3::t4::t5::t6::Nil)

        (d) must haveTheSameElementsAs (expected)
         
      }

      "an example that needs the trivial decomposition added at the end" in {
        // a, fa, f²a, f³a

        val f = ConstantStringSymbol("f")
        val a = FOLConst(new ConstantStringSymbol("a"))
        
        val fa = Function(f, a::Nil)
        val f2a = Function(f, (Function(f, a::Nil))::Nil)
        val f3a = Function(f, (Function(f, (Function(f, a::Nil))::Nil))::Nil)

        val alpha = FOLVar(new VariableStringSymbol("α"))
        val falpha = Function(f, alpha::Nil)
        val f2alpha = Function(f, (Function(f, alpha::Nil))::Nil)
        val f3alpha = Function(f, (Function(f, (Function(f, alpha::Nil))::Nil))::Nil)

        var expected : List[(List[FOLTerm], List[FOLTerm])] = Nil
        expected = expected :+ (alpha::f2alpha::Nil, a::fa::Nil)
        expected = expected :+ (alpha::f2alpha::falpha::Nil, a::fa::Nil)
        expected = expected :+ (alpha::falpha::Nil, a::f2a::Nil)
        expected = expected :+ (alpha::falpha::Nil, a::fa::f2a::Nil)

        val d = Decomposition(a::fa::f2a::f3a::Nil)

        (d) must haveTheSameElementsAs (expected)
      }

      "issue 206!!" in {
        // LinearEqExampleProof(4)
        // Term set for three formulas:
        // F1 (1 quant.) -> (a)
        // F2 (1 quant.) -> (a, fa, f²a, f³a)
        // F3 (3 quant.) -> ([fa, a, a], [f²a, fa, a], [f³a, f²a, a], [f⁴a, f³a, a])

        val f = ConstantStringSymbol("f")
        val a = FOLConst(new ConstantStringSymbol("a"))
        val alpha = FOLVar(new VariableStringSymbol("α"))
        
        val fa = Function(f, a::Nil)
        val f2a = Function(f, (Function(f, a::Nil))::Nil)
        val f3a = Function(f, (Function(f, (Function(f, a::Nil))::Nil))::Nil)
        val f4a = Function(f, Function(f, (Function(f, (Function(f, a::Nil))::Nil))::Nil)::Nil)

        // Tuple function symbols:
        val tuple1 = ConstantStringSymbol("tuple1")
        val tuple2 = ConstantStringSymbol("tuple2")
        val tuple3 = ConstantStringSymbol("tuple3")

        // Termset for F1
        val t11 = Function(tuple1, a::Nil)
        val ts1 = t11::Nil

        // Termset for F2
        val t21 = Function(tuple2, a::Nil)
        val t22 = Function(tuple2, fa::Nil)
        val t23 = Function(tuple2, f2a::Nil)
        val t24 = Function(tuple2, f3a::Nil)
        val ts2 = t21::t22::t23::t24::Nil

        // Termset for F3
        val t31 = Function(tuple3, fa::a::a::Nil)
        val t32 = Function(tuple3, f2a::fa::a::Nil)
        val t33 = Function(tuple3, f3a::f2a::a::Nil)
        val t34 = Function(tuple3, f4a::f3a::a::Nil)
        val ts3 = t31::t32::t33::t34::Nil

        val termset = ts1 ++ ts2 ++ ts3

        val d = Decomposition(termset)

        val t2alpha = Function(tuple2, alpha::Nil)
        val t3alpha = Function(tuple3, Function(f, alpha::Nil)::alpha::a::Nil)
        val criticalDecomposition = (t2alpha::t3alpha::t11::Nil, a::fa::f2a::f3a::Nil)

        d must contain (criticalDecomposition)
      }
    }
  }
}
