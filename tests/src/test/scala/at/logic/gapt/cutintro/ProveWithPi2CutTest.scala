package at.logic.gapt.cutintro
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.lk.LKProof
import org.specs2.mutable.Specification
/**
 * Created by root on 08.02.17.
 */
class ProveWithPi2CutTest extends Specification {

  /*
  */
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
      val fA1 = fof"!u (P(u)|Q(f1(u)))"
      val fB = fof"!u!v ((P(u)|Q(v))->(P(u)|Q(f(v))))"
      val fC1 = fof"!u!v ((P(u)|Q(f(v)))->(P(u)|Q(g(v))))"
      val eD = fof"?u?v ((P(u)|Q(g(v))))"
      val endSequent = fA1 +: fB +: fC1 +: Sequent() :+ eD
      val proof: Option[LKProof] = proveWithPi2Cut( endSequent, seHs, yName, xName )
      ( proof match {
        case Some( t ) => true
        case _         => false
      } ) must_== true
    }
  }

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
      val fA4 = fof"!u (P(u,f1(u))|P(u,f2(u))|P(u,f3(u))|P(u,f4(u)))"
      val fB = fof"!u!v (P(u,v)->P(u,f(v)))"
      val fC4 = fof"!u!v!w!xu ((P(u,f(v))&P(f(v),f(w))&P(f(w),f(xu)))->P(u,g(xu)))"
      val eD = fof"?u?v (P(u,g(v)))"
      val endSequent = fA4 +: fB +: fC4 +: Sequent() :+ eD
      val proof: Option[LKProof] = proveWithPi2Cut( endSequent, seHs, yName, xName )
      ( proof match {
        case Some( t ) => true
        case _         => false
      } ) must_== true
    }
  }

  /*
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
      val fA3 = fof"!u (P(u,f1(u))|P(u,f2(u))|P(u,f3(u)))"
      val fB = fof"!u!v (P(u,v)->P(u,f(v)))"
      val fC3 = fof"!u!v!w ((P(u,f(v))&P(f(v),f(w)))->P(u,g(w)))"
      val eD = fof"?u?v (P(u,g(v)))"
      val endSequent = fA3 +: fB +: fC3 +: Sequent() :+ eD
      val proof: Option[LKProof] = proveWithPi2Cut( endSequent, seHs, yName, xName )
      ( proof match {
        case Some( t ) => true
        case _         => false
      } ) must_== true
    }
  }


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
      val eT = fof"?u?v (Pkl(u,v)&Pg(f(u),f(v)))"
      val feI0 = fof"?v (Pklg(c,v)&Pg(f(v),0))"
      val fGamma1 = fof"!u!v (Pklg(u,M(u,v))&Pklg(v,M(u,v)))"
      val fGamma2 = fof"!u (Pg(f(u),0)|Pg(f(u),s(0)))"
      val fDelta1 = fof"!u!v!w ((Pg(u,v)&Pg(v,w))->Pg(u,w))"
      val fDelta2 = fof"!u!v (Pklg(s(u),v)->Pkl(u,v))"
      val fRef = fof"!u!v (Pg(u,v)->Pg(v,u))"
      val endSequent = fRef +: fGamma1 +: fGamma2 +: fDelta1 +: fDelta2 +: Sequent() :+ eT :+ feI0
      val proof: Option[LKProof] = proveWithPi2Cut( endSequent, seHs, yName, xName )
      ( proof match {
        case Some( t ) => true
        case _         => false
      } ) must_== true
    }
  }


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
      val fP = fof"!xx (((P(xx)&Q(f1(xx)))|(P(f1(xx))&Q(xx)))|((P(xx)&Q(f2(xx)))|(P(f2(xx))&Q(xx))))"
      val fPf = fof"!xx!yy (((P(xx)&Q(yy))|(P(yy)&Q(xx)))->((P(xx)&Q(f(yy)))|(P(f(yy))&Q(xx))))"
      val fPfg = fof"!x1!x2!x3 ((((P(x1)&Q(f(x2)))|(P(f(x2))&Q(x1)))&((P(f(x2))&Q(f(x3)))|(P(f(x3))&Q(f(x2)))))->((P(x1)&Q(g(x3)))|(P(g(x3))&Q(x1))))"
      val ePg = fof"?uu?vv (((P(uu)&Q(g(vv)))|(P(g(vv))&Q(uu))))"
      val endSequent = fP +: fPf +: fPfg +: Sequent() :+ ePg
      val proof: Option[LKProof] = proveWithPi2Cut( endSequent, seHs, yName, xName )
      ( proof match {
        case Some( t ) => true
        case _ => false
      }) must_== true
    }
  }
  */

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
      val fP = fof"!xx ((P(xx)&Q(f1(xx)))|(P(f1(xx))&Q(xx)))"
      val fPf = fof"!xx!yy (((P(xx)&Q(yy))|(P(yy)&Q(xx)))->((P(xx)&Q(f(yy)))|(P(f(yy))&Q(xx))))"
      val fPfg = fof"!x1!x2!x3 ((((P(x1)&Q(f(x2)))|(P(f(x2))&Q(x1)))&((P(f(x2))&Q(f(x3)))|(P(f(x3))&Q(f(x2)))))->((P(x1)&Q(g(x3)))|(P(g(x3))&Q(x1))))"
      val ePg = fof"?uu?vv (((P(uu)&Q(g(vv)))|(P(g(vv))&Q(uu))))"
      val endSequent = fP +: fPf +: fPfg +: Sequent() :+ ePg
      val proof: Option[LKProof] = proveWithPi2Cut( endSequent, seHs, yName, xName )
      ( proof match {
        case Some( t ) => true
        case _         => false
      } ) must_== true
    }
  }

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
      val fP = fof"!xx ((P(xx)&Q(f1(xx)))|(P(f1(xx))&Q(xx)))"
      val fPf = fof"!xx!yy (((P(xx)&Q(yy))|(P(yy)&Q(xx)))->((P(xx)&Q(f(yy)))|(P(f(yy))&Q(xx))))"
      val fPfg = fof"!x1!x2 ((((P(x1)&Q(f(x2)))|(P(f(x2))&Q(x1))))->((P(x1)&Q(g(x2)))|(P(g(x2))&Q(x1))))"
      val ePg = fof"?uu?vv (((P(uu)&Q(g(vv)))|(P(g(vv))&Q(uu))))"
      val endSequent = fP +: fPf +: fPfg +: Sequent() :+ ePg
      val proof: Option[LKProof] = proveWithPi2Cut( endSequent, seHs, yName, xName )
      ( proof match {
        case Some( t ) => true
        case _         => false
      } ) must_== true
    }
  }

}
