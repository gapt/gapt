package gapt.formats.tptp

import gapt.expr._
import gapt.expr.formula.Atom
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import org.specs2.mutable._

class TptpHOLExporterTest extends Specification {
  "Export to TPTP thf" should {
    "handle atoms correctly" in {
      val x = Var("x", Ti ->: To)
      val y = Var("y", To)
      val c = Const("c", Ti)

      val ax = Atom(x, List(c))
      val ay = Atom(y)

      // println( TPTPHOLExporter( List( HOLSequent( Nil, List( ax, ay ) ) ), true ) )

      /*
      println( TPTPHOLExporter( List(
        HOLSequent( List( ax ), Nil ),
        HOLSequent( Nil, List( ay ) )
      ), true ) )
       */
      ok
    }
  }

}
