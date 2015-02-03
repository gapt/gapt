package at.logic.algorithms.resolution

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import at.logic.language.lambda.types.To
import at.logic.language.fol.{Equation => FOLEquation, And, Or, Neg, Atom, FOLConst, Imp}
import at.logic.calculi.resolution.FClause
import at.logic.calculi.lk.base.FSequent

@RunWith(classOf[JUnitRunner])
class SymmetryTest extends SpecificationWithJUnit {
  "fixSymmetry" should {
    "not say that p :- is derivable from p :- p, r by symmetry" in {
      val p = Atom( "p", Nil )
      val r = Atom( "r", Nil )
      val to = FClause( p::Nil, Nil )
      val from = FSequent( p::Nil, p::r::Nil )

      fixSymmetry.canDeriveBySymmetry( to, from ) must beFalse
    }

    "say that a=b, b=c :- c=d is derivable from c=b, a=b :- d=c" in {
      val a = FOLConst("a")
      val b = FOLConst("b")
      val c = FOLConst("c")
      val d = FOLConst("d")
      val ab = FOLEquation( a, b )
      val bc = FOLEquation( b, c )
      val cd = FOLEquation( c, d )
      val cb = FOLEquation( c, b )
      val dc = FOLEquation( d, c )
      val from = FSequent( ab::bc::Nil, cd::Nil )
      val to = FClause( cb::ab::Nil, dc::Nil )

      fixSymmetry.canDeriveBySymmetry( to, from ) must beTrue
    }
  }
}
