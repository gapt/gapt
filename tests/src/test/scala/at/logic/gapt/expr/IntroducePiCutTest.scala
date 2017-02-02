package at.logic.gapt.expr

import at.logic.gapt.proofs.Sequent
import org.specs2.mutable.Specification

/**
  * Created by root on 02.02.17.
  */
class IntroducePiCutTest extends Specification {

  "This" should {
    "as well" in {
      val Pxf1x = fof"(P(x)&Q(f1(x)))|(P(f1(x))&Q(x))"
      val Pxff1x = fof"(P(x)&Q(f(f1(x))))|(P(f(f1(x)))&Q(x))"
      val Pcfy1 = fof"(P(c)&Q(f(y1)))|(P(f(y1))&Q(c))"
      val Pcgy2 = fof"(P(c)&Q(g(y1)))|(P(g(y1))&Q(c))"
      val A1 = fof"$Pxf1x"
      val B1 = fof"$Pxf1x->$Pxff1x"
      val C1 = fof"$Pcfy1->$Pcgy2"
      val D = fof"$Pcgy2"
      val Rere = A1 +: B1 +: C1 +: Sequent() :+ D
      val seHs = new pi2SeHs( Rere, fov"x", List( fov"y1" ), List( fot"c" ), List( fot"f1(x)" ) )
      val xName = fov"xName"
      val yName = fov"yName"
      introducePi2Cut( seHs, yName, xName ) must_== ( Option( fof"(P($xName)&Q(f($yName)))|(P(f($yName))&Q($xName))" ) )
    }
  }

}
