/*
* Tests for forgetful resolution.
*
*/

package at.logic.algorithms.cutIntroduction

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.fol._
import MinimizeSolution._

@RunWith(classOf[JUnitRunner])
class ForgetfulResolutionTest extends SpecificationWithJUnit {

  "Forgetful Paramodulation Should" should {

    "successfully paramodulate a=b into f(a,a)" in {
      val a = FOLConst("a")
      val b = FOLConst("b")
      val fs = "f"
      val faa = Function(fs, a::a::Nil)

      val realab = Set( Function( fs, a::a::Nil ), Function( fs, a::b::Nil ), Function( fs, b::a::Nil ), Function( fs, b::b::Nil ) )
      val realba = Set( Function( fs, a::a::Nil ) )
     
      val parasab = Paramodulants(a, b, faa)
      val parasba = Paramodulants(b, a, faa)

      parasab must beEqualTo(realab)
      parasba must beEqualTo(realba)
    }

    "successfully apply forgetful paramodulation to { :- a = b; :- P(a, a); :- Q } " in {
      val a = FOLConst("a")
      val b = FOLConst("b")
      val ps = "P"
      val paa = Atom(ps, a::a::Nil)
      val pab = Atom(ps, a::b::Nil)
      val pba = Atom(ps, b::a::Nil)
      val pbb = Atom(ps, b::b::Nil)
      val q = Atom("Q", Nil )
      val cq = new MyFClause( Nil, q::Nil )
      val cpaa = new MyFClause( Nil, paa::Nil )
      val cpab = new MyFClause( Nil, pab::Nil )
      val cpba = new MyFClause( Nil, pba::Nil )
      val cpbb = new MyFClause( Nil, pbb::Nil )

      val r1 = Set(cpab, cq)
      val r2 = Set(cpba, cq)
      val r3 = Set(cpbb, cq)
      val real = Set(r1, r2, r3)

      val res = ForgetfulParamodulateCNF( And( Equation( a, b)::paa::q::Nil ) )

      val setres = res.map( cnf => cnf.toSet ).toSet

      setres must beEqualTo(real)
    }
/*
    "improve the solution correctly" in {
      val p = at.logic.testing.LinearExampleProof(8)
      val ts = new FlatTermSet(TermsExtraction(p))
      val g = ComputeGrammars(ts)
      val grm = g(2)
      val ehs = new ExtendedHerbrandSequent(p.root, grm, ts)
      val improv = improveSolution(ehs.canonicalSol, ehs)

      // TODO: type the expected value correctly
      //val expected =
      //improv must
      success
    }
*/
  }

  "Forgetful Resolution Should" should {

    "compute a single resolvent successfully" in {
      val a = Atom("A")
      val b = Atom("B")
      val c = Atom("C")
      val d = Atom("D")
      val e = Atom("E")

      val f = And(And(Or(a,Or(b,c)), Or(Neg(b), d)), e)

      val res = ForgetfulResolve(f)

      //println("Formula (in CNF): " + f)
      //println("Resolvent: " + res)

      res.size must beEqualTo(1)
    }

/*
    "improve the solution correctly" in {
      val p = at.logic.testing.LinearExampleProof(8)
      val ts = new FlatTermSet(TermsExtraction(p))
      val g = ComputeGrammars(ts)
      val grm = g(2)
      val ehs = new ExtendedHerbrandSequent(p.root, grm, ts)
      val improv = improveSolution(ehs.canonicalSol, ehs)

      // TODO: type the expected value correctly
      //val expected =
      //improv must
      success
    }
*/
  }
}

