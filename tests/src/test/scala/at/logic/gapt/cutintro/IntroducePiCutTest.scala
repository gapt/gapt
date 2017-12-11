package at.logic.gapt.cutintro
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import org.specs2.mutable.Specification

/**
 * Created by root on 02.02.17.
 */
class IntroducePiCutTest extends Specification {

  //
  // Number of non-tautological leaves
  //   2
  // Number of unified literals
  //   2
  // Number of allowed clauses (without unnecessary clauses)
  //   2
  // Number of checked Formulas
  //   3
  "This" should {
    "be computed correctly" in {
      val Pxf1x = fof"(P(x)|Q(f1(x)))"
      val Pxff1x = fof"(P(x)|Q(f(f1(x))))"
      val Pcfy1 = fof"(P(c)|Q(f(y1)))"
      val Pcgy2 = fof"(P(c)|Q(g(y1)))"
      val A1 = fof"$Pxf1x"
      val B1 = fof"$Pxf1x->$Pxff1x"
      val C1 = fof"$Pcfy1->$Pcgy2"
      val D = fof"$Pcgy2"
      val Rere = A1 +: B1 +: C1 +: Sequent() :+ D
      val seHs = new Pi2SeHs( Rere, fov"x", List( fov"y1" ), List( fot"c" ), List( fot"f1(x)" ) )
      val xName = fov"xName"
      val yName = fov"yName"
      introducePi2Cut( seHs, yName, xName ) must beOneOf(
        ( Option( fof"P($xName)|Q(f($yName))" ), yName, xName ),
        ( Option( fof"Q(f($yName))|P($xName)" ), yName, xName ) )
    }
  }

  //
  // Number of non-tautological leaves
  //   96
  // Number of unified literals
  //   1
  // No 'allowed clauses' were computed
  // Number of checked Formulas
  //   1
  "This" should {
    "be computed correctly" in {
      val A4 = fof"P(x,f1(x))|P(x,f2(x))|P(x,f3(x))|P(x,f4(x))"
      val B1 = fof"P(x,f1(x))->P(x,f(f1(x)))"
      val B2 = fof"P(x,f2(x))->P(x,f(f2(x)))"
      val B3 = fof"P(x,f3(x))->P(x,f(f3(x)))"
      val B4 = fof"P(x,f4(x))->P(x,f(f4(x)))"
      val C4 = fof"(P(c,f(y1))&P(f(y1),f(y2))&P(f(y2),f(y3)))->P(c,g(y3))"
      val D = fof"P(c,g(y3))"
      val Rere = A4 +: B1 +: B2 +: B3 +: B4 +: C4 +: Sequent() :+ D
      val seHs = new Pi2SeHs( Rere, fov"x", List( fov"y1", fov"y2", fov"y3" ), List( fot"c", fot"f(y1)", fot"f(y2)" ), List( fot"f1(x)", fot"f2(x)", fot"f3(x)", fot"f4(x)" ) )
      val xName = fov"xName"
      val yName = fov"yName"
      introducePi2Cut( seHs, yName, xName ) must_== ( ( Option( fof"P($xName,f($yName))" ), yName, xName ) )
    }
  }

  //
  // Number of non-tautological leaves
  //   24
  // Number of unified literals
  //   1
  // No 'allowed clauses' were computed
  // Number of checked Formulas
  //   1
  "This" should {
    "be computed correctly" in {
      val A3 = fof"P(x,f1(x))|P(x,f2(x))|P(x,f3(x))"
      val B1 = fof"P(x,f1(x))->P(x,f(f1(x)))"
      val B2 = fof"P(x,f2(x))->P(x,f(f2(x)))"
      val B3 = fof"P(x,f3(x))->P(x,f(f3(x)))"
      val C3 = fof"(P(c,f(y1))&P(f(y1),f(y2)))->P(c,g(y2))"
      val D = fof"P(c,g(y2))"
      val Rere = A3 +: B1 +: B2 +: B3 +: C3 +: Sequent() :+ D
      val seHs = new Pi2SeHs( Rere, fov"x", List( fov"y1", fov"y2" ), List( fot"c", fot"f(y1)" ), List( fot"f1(x)", fot"f2(x)", fot"f3(x)" ) )
      val xName = fov"xName"
      val yName = fov"yName"
      introducePi2Cut( seHs, yName, xName ) must_== ( ( Option( fof"P($xName,f($yName))" ), yName, xName ) )
    }
  }

  //
  // Number of non-tautological leaves
  //   86
  // Number of unified literals
  //   3
  // Number of allowed clauses (without unnecessary clauses)
  //   1
  // Number of checked Formulas
  //   1
  "This" should {
    "be computed correctly" in {
      val T1 = fof"Pkl(0,y1)&Pg(f(0),f(y1))"
      val T2 = fof"Pkl(y1,y2)&Pg(f(y1),f(y2))"
      val I0 = fof"Pklg(c,M(c,x))&Pg(f(M(c,x)),0)"
      val Gamma1 = fof"Pklg(c,M(c,x))&Pklg(x,M(c,x))"
      val Gamma21 = fof"Pg(f(M(c,x)),0)|Pg(f(M(c,x)),s(0))"
      val Gamma22 = fof"Pg(f(0),0)|Pg(f(0),s(0))"
      val Gamma23 = fof"Pg(f(y1),0)|Pg(f(y1),s(0))"
      val Gamma24 = fof"Pg(f(y2),0)|Pg(f(y2),s(0))"
      val Delta11 = fof"(Pg(f(y1),0)&Pg(0,f(y2)))->Pg(f(y1),f(y2))"
      val Delta12 = fof"(Pg(f(y1),s(0))&Pg(s(0),f(y2)))->Pg(f(y1),f(y2))"
      val Delta13 = fof"(Pg(f(0),0)&Pg(0,f(y1)))->Pg(f(0),f(y1))"
      val Delta14 = fof"(Pg(f(0),s(0))&Pg(s(0),f(y1)))->Pg(f(0),f(y1))"
      val Delta21 = fof"Pklg(s(0),y1)->Pkl(0,y1)"
      val Delta22 = fof"Pklg(s(y1),y2)->Pkl(y1,y2)"
      val Ref1 = fof"Pg(f(y1),0)->Pg(0,f(y1))"
      val Ref2 = fof"Pg(f(y2),0)->Pg(0,f(y2))"
      val Ref3 = fof"Pg(f(y1),s(0))->Pg(s(0),f(y1))"
      val Ref4 = fof"Pg(f(y2),s(0))->Pg(s(0),f(y2))"
      val Rere = Ref1 +: Ref2 +: Ref3 +: Ref4 +: Gamma1 +: Gamma21 +: Gamma22 +: Gamma23 +: Gamma24 +: Delta11 +: Delta12 +: Delta13 +: Delta14 +: Delta21 +: Delta22 +: Sequent() :+ T1 :+ T2 :+ I0
      val seHs = new Pi2SeHs( Rere, fov"x", List( fov"y1", fov"y2" ), List( fot"0", fot"s(y1)" ), List( fot"M(c,x)" ) )
      val xName = fov"xName"
      val yName = fov"yName"
      introducePi2Cut( seHs, yName, xName ) must beOneOf(
        ( Option( fof"Pklg($xName,$yName)&Pg(f($yName),s(0))" ), yName, xName ),
        ( Option( fof"Pg(f($yName),s(0))&Pklg($xName,$yName)" ), yName, xName ) )
    }
  }

  /*
  //
  // Number of non-tautological leaves
  //   1386
  // Number of unified literals
  //   6
  // Number of allowed clauses (without unnecessary clauses)
  //   7
  // Number of checked Formulas
  //   8
  "This" should {
    "be computed correctly" in {
      val Pxf1x = fof"(P(x)&Q(f1(x)))|(P(f1(x))&Q(x))"
      val Pxf2x = fof"(P(x)&Q(f2(x)))|(P(f2(x))&Q(x))"
      val Pxf3x = fof"(P(x)&Q(f3(x)))|(P(f3(x))&Q(x))"
      val Pxff1x = fof"(P(x)&Q(f(f1(x))))|(P(f(f1(x)))&Q(x))"
      val Pxff2x = fof"(P(x)&Q(f(f2(x))))|(P(f(f2(x)))&Q(x))"
      val Pxff3x = fof"(P(x)&Q(f(f3(x))))|(P(f(f3(x)))&Q(x))"
      val Pcfy1 = fof"(P(c)&Q(f(y1)))|(P(f(y1))&Q(c))"
      val Pfy1fy2 = fof"(P(f(y1))&Q(f(y2)))|(P(f(y2))&Q(f(y1)))"
      val Pcgy2 = fof"(P(c)&Q(g(y2)))|(P(g(y2))&Q(c))"
      val A3 = fof"$Pxf1x|$Pxf2x|$Pxf3x"
      val B1 = fof"$Pxf1x->$Pxff1x"
      val B2 = fof"$Pxf2x->$Pxff2x"
      val B3 = fof"$Pxf3x->$Pxff3x"
      val C3 = fof"$Pcfy1&$Pfy1fy2->$Pcgy2"
      val D = fof"$Pcgy2"
      val Rere = A3 +: B1 +: B2 +: B3 +: C3 +: Sequent() :+ D
      val seHs = new Pi2SeHs( Rere, fov"x", List( fov"y1", fov"y2" ), List( fot"c", fot"f(y1)" ), List( fot"f1(x)", fot"f2(x)", fot"f3(x)" ) )
      val xName = fov"xName"
      val yName = fov"yName"
      introducePi2Cut( seHs, yName, xName ) must beOneOf (
        (Option( fof"P($xName)&Q(f($yName))|P(f($yName))&Q($xName)" ),yName,xName),
        (Option( fof"P($xName)&Q(f($yName))|Q($xName)&P(f($yName))" ),yName,xName),
        (Option( fof"Q(f($yName))&P($xName)|P(f($yName))&Q($xName)" ),yName,xName),
        (Option( fof"Q(f($yName))&P($xName)|Q($xName)&P(f($yName))" ),yName,xName),
        (Option( fof"P(f($yName))&Q($xName)|P($xName)&Q(f($yName))" ),yName,xName),
        (Option( fof"Q($xName)&P(f($yName))|P($xName)&Q(f($yName))" ),yName,xName),
        (Option( fof"P(f($yName))&Q($xName)|Q(f($yName))&P($xName)" ),yName,xName),
        (Option( fof"Q($xName)&P(f($yName))|Q(f($yName))&P($xName)" ),yName,xName)
      )
    }
  }

  //
  // Number of non-tautological leaves
  //   308
  // Number of unified literals
  //   6
  // Number of allowed clauses (without unnecessary clauses)
  //   7
  // Number of checked Formulas
  //   14
  "This" should {
    "be computed correctly" in {
      val Pxf1x = fof"(P(x)&Q(f1(x)))|(P(f1(x))&Q(x))"
      val Pxf2x = fof"(P(x)&Q(f2(x)))|(P(f2(x))&Q(x))"
      val Pxff1x = fof"(P(x)&Q(f(f1(x))))|(P(f(f1(x)))&Q(x))"
      val Pxff2x = fof"(P(x)&Q(f(f2(x))))|(P(f(f2(x)))&Q(x))"
      val Pcfy1 = fof"(P(c)&Q(f(y1)))|(P(f(y1))&Q(c))"
      val Pfy1fy2 = fof"(P(f(y1))&Q(f(y2)))|(P(f(y2))&Q(f(y1)))"
      val Pcgy2 = fof"(P(c)&Q(g(y2)))|(P(g(y2))&Q(c))"
      val A2 = fof"$Pxf1x|$Pxf2x"
      val B1 = fof"$Pxf1x->$Pxff1x"
      val B2 = fof"$Pxf2x->$Pxff2x"
      val C3 = fof"$Pcfy1&$Pfy1fy2->$Pcgy2"
      val D = fof"$Pcgy2"
      val Rere = A2 +: B1 +: B2 +: C3 +: Sequent() :+ D
      val seHs = new Pi2SeHs( Rere, fov"x", List( fov"y1", fov"y2" ), List( fot"c", fot"f(y1)" ), List( fot"f1(x)", fot"f2(x)" ) )
      val xName = fov"xName"
      val yName = fov"yName"
      introducePi2Cut( seHs, yName, xName ) must beOneOf (
        (Option( fof"P($xName)&Q(f($yName))|P(f($yName))&Q($xName)" ),yName,xName),
        (Option( fof"P($xName)&Q(f($yName))|Q($xName)&P(f($yName))" ),yName,xName),
        (Option( fof"Q(f($yName))&P($xName)|P(f($yName))&Q($xName)" ),yName,xName),
        (Option( fof"Q(f($yName))&P($xName)|Q($xName)&P(f($yName))" ),yName,xName),
        (Option( fof"P(f($yName))&Q($xName)|P($xName)&Q(f($yName))" ),yName,xName),
        (Option( fof"Q($xName)&P(f($yName))|P($xName)&Q(f($yName))" ),yName,xName),
        (Option( fof"P(f($yName))&Q($xName)|Q(f($yName))&P($xName)" ),yName,xName),
        (Option( fof"Q($xName)&P(f($yName))|Q(f($yName))&P($xName)" ),yName,xName)
      )
    }
  }

  //
  // Number of non-tautological leaves
  //   44
  // Number of unified literals
  //   4
  // Number of allowed clauses (without unnecessary clauses)
  //   7
  // Number of checked Formulas
  //   18
  "This" should {
    "be computed correctly" in {
      val Pxf1x = fof"(P(x)&Q(f1(x)))|(P(f1(x))&Q(x))"
      val Pxff1x = fof"(P(x)&Q(f(f1(x))))|(P(f(f1(x)))&Q(x))"
      val Pcfy1 = fof"(P(c)&Q(f(y1)))|(P(f(y1))&Q(c))"
      val Pfy1fy2 = fof"(P(f(y1))&Q(f(y2)))|(P(f(y2))&Q(f(y1)))"
      val Pcgy2 = fof"(P(c)&Q(g(y2)))|(P(g(y2))&Q(c))"
      val A1 = fof"$Pxf1x"
      val B1 = fof"$Pxf1x->$Pxff1x"
      val C3 = fof"$Pcfy1&$Pfy1fy2->$Pcgy2"
      val D = fof"$Pcgy2"
      val Rere = A1 +: B1 +: C3 +: Sequent() :+ D
      val seHs = new Pi2SeHs( Rere, fov"x", List( fov"y1", fov"y2" ), List( fot"c", fot"f(y1)" ), List( fot"f1(x)" ) )
      val xName = fov"xName"
      val yName = fov"yName"
      introducePi2Cut( seHs, yName, xName ) must beOneOf(
        ( Option( fof"P($xName)&Q(f($yName))|P(f($yName))&Q($xName)" ), yName, xName ),
        ( Option( fof"P($xName)&Q(f($yName))|Q($xName)&P(f($yName))" ), yName, xName ),
        ( Option( fof"Q(f($yName))&P($xName)|P(f($yName))&Q($xName)" ), yName, xName ),
        ( Option( fof"Q(f($yName))&P($xName)|Q($xName)&P(f($yName))" ), yName, xName ),
        ( Option( fof"P(f($yName))&Q($xName)|P($xName)&Q(f($yName))" ), yName, xName ),
        ( Option( fof"Q($xName)&P(f($yName))|P($xName)&Q(f($yName))" ), yName, xName ),
        ( Option( fof"P(f($yName))&Q($xName)|Q(f($yName))&P($xName)" ), yName, xName ),
        ( Option( fof"Q($xName)&P(f($yName))|Q(f($yName))&P($xName)" ), yName, xName )
      )
    }
  }

  //
  // Number of non-tautological leaves
  //   16
  // Number of unified literals
  //   4
  // Number of allowed clauses (without unnecessary clauses)
  //   5
  // Number of checked Formulas
  //   12
  "This" should {
    "be computed correctly" in {
      val Pxf1x = fof"(P(x)&Q(f1(x)))|(P(f1(x))&Q(x))"
      val Pxff1x = fof"(P(x)&Q(f(f1(x))))|(P(f(f1(x)))&Q(x))"
      val Pcfy1 = fof"(P(c)&Q(f(y1)))|(P(f(y1))&Q(c))"
      val Pcgy1 = fof"(P(c)&Q(g(y1)))|(P(g(y1))&Q(c))"
      val A1 = fof"$Pxf1x"
      val B1 = fof"$Pxf1x->$Pxff1x"
      val C2 = fof"$Pcfy1->$Pcgy1"
      val D = fof"$Pcgy1"
      val Rere = A1 +: B1 +: C2 +: Sequent() :+ D
      val seHs = new Pi2SeHs( Rere, fov"x", List( fov"y1" ), List( fot"c" ), List( fot"f1(x)" ) )
      val xName = fov"xName"
      val yName = fov"yName"
      introducePi2Cut( seHs, yName, xName ) must beOneOf(
        ( Option( fof"P($xName)&Q(f($yName))|P(f($yName))&Q($xName)" ), yName, xName ),
        ( Option( fof"P($xName)&Q(f($yName))|Q($xName)&P(f($yName))" ), yName, xName ),
        ( Option( fof"Q(f($yName))&P($xName)|P(f($yName))&Q($xName)" ), yName, xName ),
        ( Option( fof"Q(f($yName))&P($xName)|Q($xName)&P(f($yName))" ), yName, xName ),
        ( Option( fof"P(f($yName))&Q($xName)|P($xName)&Q(f($yName))" ), yName, xName ),
        ( Option( fof"Q($xName)&P(f($yName))|P($xName)&Q(f($yName))" ), yName, xName ),
        ( Option( fof"P(f($yName))&Q($xName)|Q(f($yName))&P($xName)" ), yName, xName ),
        ( Option( fof"Q($xName)&P(f($yName))|Q(f($yName))&P($xName)" ), yName, xName )
      )
    }
  }
  */

}
