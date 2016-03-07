package at.logic.gapt.examples

// A scala script which generates hard problems for higher order theorem provers
// Formulas:
//   f1,f2       ... if-then-else axiomatizations
//   f3,f4       ... properties of the successor function (0 is no successor and
//                     a number is always different from its successor)
//   conclusion0 ... there exists a function h s.t. h(0) = 1, h(1) = 0
//   conclusion1 ... there exists a function h s.t. h(0) = 1, h(1) = 0, h(2) = 0
//   conclusion2 ... there exists a function h s.t. h(0) = 1, h(1) = 0, h(2) = 1
//   w1          ... witness for sc
//   w2          ... witness for sc2

import java.io._

import at.logic.gapt.formats.llkNew.short._
import at.logic.gapt.formats.tptp.TPTPHOLExporter
import at.logic.gapt.proofs.HOLSequent

object nTape6 {

  implicit val signature =
    sig( """var X:o; var U,V:i; var H:i>i; var x,y:i;
              const zero:i; const s:i>i;  const h:i>i;
              const ite : o > (i > (i>i));""" )
  val s1 = "(all X all U all V (X -> ite(X,U,V) = U))"
  val s2 = "(all X all U all V (-X -> ite(X,U,V) = V))"
  val s3 = "(all x -(s(x) = zero))"
  val s4 = "(all x -(s(x) = x))"
  val s5 = "(all x (h(x) = ite((x=zero), s(zero), zero) ))"
  val s6 = "(all x (h(x) = ite((x=s(zero)), zero, s(zero)) ))"
  val s7 =
    """(all x (h(x) = ite((x=zero), s(zero),
                            ite((x=s(zero)), zero, s(zero)  ))))"""

  val sc = "(exists H (H(zero)=s(zero) & H(s(zero))=zero ))"
  val sc1 = "(exists H (H(zero)=s(zero) & H(s(zero))=zero & H(s(s(zero))) = zero))"
  val sc2 = "(exists H (H(zero)=s(zero) & H(s(zero))=zero & H(s(s(zero))) = s(zero)))"

  val List( f1, f2, f3, f4, w1, w2, w3, conclusion0, conclusion1, conclusion2 ) =
    List( s1, s2, s3, s4, s5, s6, s7, sc, sc1, sc2 ).map( hof( _ ) )

  val s0a = HOLSequent( f1 :: f2 :: Nil, conclusion0 :: Nil )
  val s0b = HOLSequent( f1 :: f2 :: w1 :: Nil, conclusion0 :: Nil )

  val s1a = HOLSequent( f1 :: f2 :: Nil, conclusion1 :: Nil )
  val s1b = HOLSequent( f1 :: f2 :: w1 :: Nil, conclusion1 :: Nil )
  val s1c = HOLSequent( f1 :: f2 :: f3 :: f4 :: w1 :: Nil, conclusion1 :: Nil )
  val s1d = HOLSequent( f1 :: f2 :: f3 :: f4 :: Nil, conclusion1 :: Nil )

  val s2b = HOLSequent( f1 :: f2 :: f4 :: w2 :: Nil, conclusion2 :: Nil )
  val s2c = HOLSequent( f1 :: f2 :: f4 :: Nil, conclusion2 :: Nil )
  val s2d = HOLSequent( f1 :: f2 :: w3 :: Nil, conclusion2 :: Nil )
  val s2e = HOLSequent( f1 :: f2 :: f3 :: f4 :: w3 :: Nil, conclusion2 :: Nil )

  val consistent = HOLSequent( f1 :: f2 :: f3 :: f4 :: w1 :: conclusion0 :: Nil, Nil )

  val cuts0a = HOLSequent( f1 :: f2 :: f3 :: f4 :: Nil, w1 :: Nil )
  val cuts0b = HOLSequent( f3 :: f4 :: w1 :: Nil, conclusion0 :: Nil )

  val fn = "ite-export-"

  def export( path: String = "." ) {
    val f = path + File.separator + fn
    //sc
    TPTPHOLExporter( List( s0a ), f + "0-minimal.tptp", true ) //provable by agsyhol
    TPTPHOLExporter( List( s0b ), f + "0-with-witness.tptp", true ) //provable by agsyhol
    //sc1
    TPTPHOLExporter( List( s1a ), f + "1-minimal.tptp", true ) //timeout
    TPTPHOLExporter( List( s1b ), f + "1-withness-no-arith.tptp", true ) //timeout
    TPTPHOLExporter( List( s1c ), f + "1-with-witness.tptp", true ) //provable by leo 2, satallax, agsyhol
    TPTPHOLExporter( List( s1d ), f + "1-without-witness.tptp", true ) //timeout
    //sc2
    TPTPHOLExporter( List( s2b ), f + "2-with-witness.tptp", true ) //provable by leo 2, satallax
    TPTPHOLExporter( List( s2c ), f + "2-without-witness.tptp", true ) //timeout
    TPTPHOLExporter( List( s2d ), f + "2-with-witness2.tptp", true ) //provable by leo 2, satallax
    TPTPHOLExporter( List( s2e ), f + "2-with-witness2-help.tptp", true ) //provable by leo 2, satallax
    //fol version
    TPTPHOLExporter( List( cuts0a ), f + "0-cut1.tptp", true )
    TPTPHOLExporter( List( cuts0b ), f + "0-cut2.tptp", true )
    TPTPHOLExporter( List( consistent ), f + "0-consistent.tptp", true )
  }
}