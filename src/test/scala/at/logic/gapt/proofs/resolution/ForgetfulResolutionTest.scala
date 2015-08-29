/*
* Tests for forgetful resolution.
*
*/

package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.CNFp
import org.specs2.mutable._

class ForgetfulResolutionTest extends Specification {

  "Forgetful Paramodulation Should" should {

    "successfully paramodulate a=b into f(a,a)" in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val fs = "f"
      val faa = FOLFunction( fs, a :: a :: Nil )

      val realab = Set( FOLFunction( fs, a :: a :: Nil ), FOLFunction( fs, a :: b :: Nil ), FOLFunction( fs, b :: a :: Nil ), FOLFunction( fs, b :: b :: Nil ) )
      val realba = Set( FOLFunction( fs, a :: a :: Nil ) )

      val parasab = Paramodulants( a, b, faa )
      val parasba = Paramodulants( b, a, faa )

      parasab must beEqualTo( realab )
      parasba must beEqualTo( realba )
    }

    "successfully apply forgetful paramodulation to { :- a = b; :- P(a, a); :- Q } " in {
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val ps = "P"
      val paa = FOLAtom( ps, a :: a :: Nil )
      val pab = FOLAtom( ps, a :: b :: Nil )
      val pba = FOLAtom( ps, b :: a :: Nil )
      val pbb = FOLAtom( ps, b :: b :: Nil )
      val q = FOLAtom( "Q", Nil )
      val cq = new Clause( Nil, q :: Nil )
      val cpaa = new Clause( Nil, paa :: Nil )
      val cpab = new Clause( Nil, pab :: Nil )
      val cpba = new Clause( Nil, pba :: Nil )
      val cpbb = new Clause( Nil, pbb :: Nil )

      val r1 = Set( cpab, cq )
      val r2 = Set( cpba, cq )
      val r3 = Set( cpbb, cq )
      val real = Set( r1, r2, r3 )

      val res = ForgetfulParamodulate( CNFp.toClauseList( And( Eq( a, b ) :: paa :: q :: Nil ) ) )

      val setres = res.map( cnf => cnf.toSet ).toSet

      setres must beEqualTo( real )
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
      val a = FOLAtom( "A" )
      val b = FOLAtom( "B" )
      val c = FOLAtom( "C" )
      val d = FOLAtom( "D" )
      val e = FOLAtom( "E" )

      val f = And( And( Or( a, Or( b, c ) ), Or( Neg( b ), d ) ), e )

      val res = ForgetfulResolve( f )

      res.size must beEqualTo( 1 )
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

