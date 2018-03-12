package gapt.cutintro
import gapt.expr._
import gapt.proofs.Sequent
import gapt.proofs.lk.LKProof
import org.specs2.mutable.Specification

class ProveWithPi2CutTest extends Specification {

  "example 1" in {
    val Ga = fof"!x!y!z ((P(x,f1(x))|P(x,f2(x)))&(P(y,z)->P(y,f(z))))"
    val De = fof"?u?v?w (-((P(u,f(v))&P(f(v),f(w)))->P(u,g(w))) | P(u,g(w)))"
    val endSequent = Ga +: Sequent() :+ De
    val Ga1 = fof"(P(xa,f1(xa))|P(xa,f2(xa)))&(P(xa,f1(xa)) -> P(xa,f(f1(xa))))"
    val Ga2 = fof"(P(xa,f1(xa))|P(xa,f2(xa)))&(P(xa,f2(xa)) ->P(xa,f(f2(xa))))"
    val De1 = fof"-((P(c,f(xb1))&P(f(xb1),f(xb2)))->P(c,g(xb2))) | P(c,g(xb2))"
    val Rere = Ga1 +: Ga2 +: Sequent() :+ De1
    val seHs = Pi2SeHs( Rere, fov"xa", List( fov"xb1", fov"xb2" ), List( fot"c", fot"f(xb1)" ), List( fot"f1(xa)", fot"f2(xa)" ) )
    proveWithPi2Cut( endSequent, seHs ) must beSome
  }

  "example 2" in {
    val Pxf1x = fof"(P(x)|Q(f1(x)))"
    val Pxff1x = fof"(P(x)|Q(f(f1(x))))"
    val Pcfy1 = fof"(P(c)|Q(f(y1)))"
    val Pcgy2 = fof"(P(c)|Q(g(y1)))"
    val A1 = fof"$Pxf1x"
    val B1 = fof"$Pxf1x->$Pxff1x"
    val C1 = fof"$Pcfy1->$Pcgy2"
    val D = fof"$Pcgy2"
    val Rere = A1 +: B1 +: C1 +: Sequent() :+ D
    val seHs = Pi2SeHs( Rere, fov"x", List( fov"y1" ), List( fot"c" ), List( fot"f1(x)" ) )
    val xName = fov"xName"
    val yName = fov"yName"
    val fA1 = fof"!u (P(u)|Q(f1(u)))"
    val fB = fof"!u!v ((P(u)|Q(v))->(P(u)|Q(f(v))))"
    val fC1 = fof"!u!v ((P(u)|Q(f(v)))->(P(u)|Q(g(v))))"
    val eD = fof"?u?v ((P(u)|Q(g(v))))"
    val endSequent = fA1 +: fB +: fC1 +: Sequent() :+ eD
    proveWithPi2Cut( endSequent, seHs, yName, xName ) must beSome
  }

  "example 3" in {
    val A4 = fof"P(x,f1(x))|P(x,f2(x))|P(x,f3(x))|P(x,f4(x))"
    val B1 = fof"P(x,f1(x))->P(x,f(f1(x)))"
    val B2 = fof"P(x,f2(x))->P(x,f(f2(x)))"
    val B3 = fof"P(x,f3(x))->P(x,f(f3(x)))"
    val B4 = fof"P(x,f4(x))->P(x,f(f4(x)))"
    val C4 = fof"(P(c,f(y1))&P(f(y1),f(y2))&P(f(y2),f(y3)))->P(c,g(y3))"
    val D = fof"P(c,g(y3))"
    val Rere = A4 +: B1 +: B2 +: B3 +: B4 +: C4 +: Sequent() :+ D
    val seHs = Pi2SeHs( Rere, fov"x", List( fov"y1", fov"y2", fov"y3" ), List( fot"c", fot"f(y1)", fot"f(y2)" ), List( fot"f1(x)", fot"f2(x)", fot"f3(x)", fot"f4(x)" ) )
    val xName = fov"xName"
    val yName = fov"yName"
    val fA4 = fof"!u (P(u,f1(u))|P(u,f2(u))|P(u,f3(u))|P(u,f4(u)))"
    val fB = fof"!u!v (P(u,v)->P(u,f(v)))"
    val fC4 = fof"!u!v!w!xu ((P(u,f(v))&P(f(v),f(w))&P(f(w),f(xu)))->P(u,g(xu)))"
    val eD = fof"?u?v (P(u,g(v)))"
    val endSequent = fA4 +: fB +: fC4 +: Sequent() :+ eD
    proveWithPi2Cut( endSequent, seHs, yName, xName ) must beSome
  }

  "example 4" in {
    val A3 = fof"P(x,f1(x))|P(x,f2(x))|P(x,f3(x))"
    val B1 = fof"P(x,f1(x))->P(x,f(f1(x)))"
    val B2 = fof"P(x,f2(x))->P(x,f(f2(x)))"
    val B3 = fof"P(x,f3(x))->P(x,f(f3(x)))"
    val C3 = fof"(P(c,f(y1))&P(f(y1),f(y2)))->P(c,g(y2))"
    val D = fof"P(c,g(y2))"
    val Rere = A3 +: B1 +: B2 +: B3 +: C3 +: Sequent() :+ D
    val seHs = Pi2SeHs( Rere, fov"x", List( fov"y1", fov"y2" ), List( fot"c", fot"f(y1)" ), List( fot"f1(x)", fot"f2(x)", fot"f3(x)" ) )
    val xName = fov"xName"
    val yName = fov"yName"
    val fA3 = fof"!u (P(u,f1(u))|P(u,f2(u))|P(u,f3(u)))"
    val fB = fof"!u!v (P(u,v)->P(u,f(v)))"
    val fC3 = fof"!u!v!w ((P(u,f(v))&P(f(v),f(w)))->P(u,g(w)))"
    val eD = fof"?u?v (P(u,g(v)))"
    val endSequent = fA3 +: fB +: fC3 +: Sequent() :+ eD
    proveWithPi2Cut( endSequent, seHs, yName, xName ) must beSome
  }

  "pigeonhole" in {
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
    val seHs = Pi2SeHs( Rere, fov"x", List( fov"y1", fov"y2" ), List( fot"0", fot"s(y1)" ), List( fot"M(c,x)" ) )
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
    proveWithPi2Cut( endSequent, seHs, yName, xName ) must beSome
  }

  "example 5" in {
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
    val seHs = Pi2SeHs( Rere, fov"x", List( fov"y1", fov"y2" ), List( fot"c", fot"f(y1)" ), List( fot"f1(x)", fot"f2(x)" ) )
    val xName = fov"xName"
    val yName = fov"yName"
    val fP = fof"!xx (((P(xx)&Q(f1(xx)))|(P(f1(xx))&Q(xx)))|((P(xx)&Q(f2(xx)))|(P(f2(xx))&Q(xx))))"
    val fPf = fof"!xx!yy (((P(xx)&Q(yy))|(P(yy)&Q(xx)))->((P(xx)&Q(f(yy)))|(P(f(yy))&Q(xx))))"
    val fPfg = fof"!x1!x2!x3 ((((P(x1)&Q(f(x2)))|(P(f(x2))&Q(x1)))&((P(f(x2))&Q(f(x3)))|(P(f(x3))&Q(f(x2)))))->((P(x1)&Q(g(x3)))|(P(g(x3))&Q(x1))))"
    val ePg = fof"?uu?vv (((P(uu)&Q(g(vv)))|(P(g(vv))&Q(uu))))"
    val endSequent = fP +: fPf +: fPfg +: Sequent() :+ ePg
    proveWithPi2Cut( endSequent, seHs, yName, xName ) must beSome
  }

  "example 6" in {
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
    val seHs = Pi2SeHs( Rere, fov"x", List( fov"y1", fov"y2" ), List( fot"c", fot"f(y1)" ), List( fot"f1(x)" ) )
    val xName = fov"xName"
    val yName = fov"yName"
    val fP = fof"!xx ((P(xx)&Q(f1(xx)))|(P(f1(xx))&Q(xx)))"
    val fPf = fof"!xx!yy (((P(xx)&Q(yy))|(P(yy)&Q(xx)))->((P(xx)&Q(f(yy)))|(P(f(yy))&Q(xx))))"
    val fPfg = fof"!x1!x2!x3 ((((P(x1)&Q(f(x2)))|(P(f(x2))&Q(x1)))&((P(f(x2))&Q(f(x3)))|(P(f(x3))&Q(f(x2)))))->((P(x1)&Q(g(x3)))|(P(g(x3))&Q(x1))))"
    val ePg = fof"?uu?vv (((P(uu)&Q(g(vv)))|(P(g(vv))&Q(uu))))"
    val endSequent = fP +: fPf +: fPfg +: Sequent() :+ ePg
    proveWithPi2Cut( endSequent, seHs, yName, xName ) must beSome
  }

  "example 7" in {
    val Pxf1x = fof"(P(x)&Q(f1(x)))|(P(f1(x))&Q(x))"
    val Pxff1x = fof"(P(x)&Q(f(f1(x))))|(P(f(f1(x)))&Q(x))"
    val Pcfy1 = fof"(P(c)&Q(f(y1)))|(P(f(y1))&Q(c))"
    val Pcgy1 = fof"(P(c)&Q(g(y1)))|(P(g(y1))&Q(c))"
    val A1 = fof"$Pxf1x"
    val B1 = fof"$Pxf1x->$Pxff1x"
    val C2 = fof"$Pcfy1->$Pcgy1"
    val D = fof"$Pcgy1"
    val Rere = A1 +: B1 +: C2 +: Sequent() :+ D
    val seHs = Pi2SeHs( Rere, fov"x", List( fov"y1" ), List( fot"c" ), List( fot"f1(x)" ) )
    val xName = fov"xName"
    val yName = fov"yName"
    val fP = fof"!xx ((P(xx)&Q(f1(xx)))|(P(f1(xx))&Q(xx)))"
    val fPf = fof"!xx!yy (((P(xx)&Q(yy))|(P(yy)&Q(xx)))->((P(xx)&Q(f(yy)))|(P(f(yy))&Q(xx))))"
    val fPfg = fof"!x1!x2 ((((P(x1)&Q(f(x2)))|(P(f(x2))&Q(x1))))->((P(x1)&Q(g(x2)))|(P(g(x2))&Q(x1))))"
    val ePg = fof"?uu?vv (((P(uu)&Q(g(vv)))|(P(g(vv))&Q(uu))))"
    val endSequent = fP +: fPf +: fPfg +: Sequent() :+ ePg
    proveWithPi2Cut( endSequent, seHs, yName, xName ) must beSome
  }

  "example 8" in {
    skipped( "this takes too long" )
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
    val seHs = Pi2SeHs( Rere, fov"x", List( fov"y1", fov"y2" ), List( fot"c", fot"f(y1)" ), List( fot"f1(x)", fot"f2(x)", fot"f3(x)" ) )
    val xName = fov"xName"
    val yName = fov"yName"
    val fP = fof"!xx (((P(xx)&Q(f1(xx)))|(P(f1(xx))&Q(xx)))|((P(xx)&Q(f2(xx)))|(P(f2(xx))&Q(xx)))|((P(xx)&Q(f3(xx)))|(P(f3(xx))&Q(xx))))"
    val fPf = fof"!xx!yy (((P(xx)&Q(yy))|(P(yy)&Q(xx)))->((P(xx)&Q(f(yy)))|(P(f(yy))&Q(xx))))"
    val fPfg = fof"!x1!x2!x3 ((((P(x1)&Q(f(x2)))|(P(f(x2))&Q(x1)))&((P(f(x2))&Q(f(x3)))|(P(f(x3))&Q(f(x2)))))->((P(x1)&Q(g(x3)))|(P(g(x3))&Q(x1))))"
    val ePg = fof"?uu?vv (((P(uu)&Q(g(vv)))|(P(g(vv))&Q(uu))))"
    val endSequent = fP +: fPf +: fPfg +: Sequent() :+ ePg
    proveWithPi2Cut( endSequent, seHs, yName, xName ) must beSome
  }

}
