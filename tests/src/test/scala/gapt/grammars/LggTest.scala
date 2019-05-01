package gapt.grammars

import gapt.expr._
import gapt.expr.ty.TBase
import gapt.expr.util.freeVariables
import gapt.proofs.context.Context
import org.specs2.mutable.Specification

class LggTest extends Specification {
  "leastGeneralGeneralization" should {
    "compute lgg of first-order terms" in {
      val ( lgg, substs ) = leastGeneralGeneralization( le"f c c", le"f d d" )
      val Seq( x ) = freeVariables( lgg ).toSeq
      lgg must_== le"f $x $x"
    }
    "compute lgg of many-sorted terms" in {
      implicit var ctx = Context.empty
      ctx += TBase( "Data" )
      ctx += TBase( "Tree" )
      ctx += hoc"Node: Data>Tree>Tree > Tree"

      ctx += hoc"a: Data"
      ctx += hoc"t: Tree"
      ctx += hoc"s: Tree"

      val ( lgg, _ ) = leastGeneralGeneralization( le"Node a t t", le"Node a s s" )
      val Seq( x ) = freeVariables( lgg ).toSeq
      lgg must_== le"Node a $x $x"
    }

    "terms with free variables" in {
      val a = le"f(x1, c)"
      val b = le"f(x1, d)"
      val ( lgg, substs ) = leastGeneralGeneralization( a, b )
      substs( a )( lgg ) must_== a
      substs( b )( lgg ) must_== b
    }
  }

  "leastGeneralGeneralization1" should {
    "terms with free variables" in {
      val a = le"f(x, c)"
      val b = le"f(x, d)"
      val ( lgg, substs ) = leastGeneralGeneralization( a, b )
      substs( a )( lgg ) must_== a
      substs( b )( lgg ) must_== b
    }
  }
}
