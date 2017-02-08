package at.logic.gapt.expr
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.lk.LKProof
import org.specs2.mutable.Specification
/**
  * Created by root on 08.02.17.
  */
class ProveWithPi2CutTest extends Specification {

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
      val eT = fof"?u?v Pkl(u,v)&Pg(f(u),f(v))"
      val feI0 = fof"?v Pkl(c,v)&Pg(f(v),0)"
      val fGamma1 = fof"!u!v Pklg(u,M(u,v))&Pklg(v,M(u,v))"
      val fGamma2 = fof"!u Pg(f(u),0)|Pg(f(u),s(0))"
      val fDelta1 = fof"!u!v!w (Pg(u,v)&Pg(v,w))->Pg(u,w)"
      val fDelta2 = fof"!u!v Pklg(s(u),v)->Pkl(u,v)"
      val fRef = fof"!u!v Pg(u,v)->Pg(v,u)"
      val endSequent = fRef +: fGamma1 +: fGamma2 +: fDelta1 +: fDelta2 +: Sequent() :+ eT :+ feI0
      val proof: Option[LKProof] = proveWithPi2Cut( endSequent, seHs, yName, xName )
      (proof match {
        case Some( t ) => true
        case _ => false
      })must_==true
    }
  }

}
