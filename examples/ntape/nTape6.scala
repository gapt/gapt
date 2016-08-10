package at.logic.gapt.examples

import java.io._

import at.logic.gapt.formats.llk.short._
import at.logic.gapt.formats.tptp.TPTPHOLExporter
import at.logic.gapt.proofs.HOLSequent

/**
 * The object nTape6 generates hard problems for higher order theorem provers containing an axiomatization of
 * if-then-else.
 * Formulas:
 * f1,f2       ... if-then-else axiomatizations
 * f3,f4       ... properties of the successor function (0 is no successor and
 * a number is always different from its successor)
 * conclusion0 ... there exists a function h s.t. h(0) = 1, h(1) = 0
 * conclusion1 ... there exists a function h s.t. h(0) = 1, h(1) = 0, h(2) = 0
 * conclusion2 ... there exists a function h s.t. h(0) = 1, h(1) = 0, h(2) = 1
 * w1          ... witness for sc
 * w2          ... witness for sc2
 *
 * The problems are (in sequent notation):
 *
 * P0: f1, f2 :- conclusion0
 * P1: f1, f2, f3, f4 :- conclusion1
 * P2: f1, f2, f3, f4 :- conclusion2
 *
 * The generated filenames are "ntape6-${i}-without-witness.tptp" for i = 0 to 2.
 *
 * To show that there are actual witnesses for the function h, we provide a witness, where the witness w1 can be used
 * for both W0 and W1:
 *
 * W0: { w1 :- } x P0
 * W1: { w1 :- } x P1
 * W2: { w2 :- } x P2
 *
 * The generated filenames are "ntape6-${i}-with-witness.tptp" for i = 0 to 2.
 */
object nTape6 {

  /**
   * Contains all the formulas used.
   */
  object formulas {
    implicit val signature =
      sig(
        """var X:o; var U,V:i; var H:i>i; var x,y:i;
              const zero:i; const s:i>i;  const h:i>i;
              const ite : o > (i > (i>i));"""
      )
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
  }

  /**
   * Contains all the conjecture sequents used.
   */
  object sequents {
    import formulas._
    val s0a = HOLSequent( f1 :: f2 :: Nil, conclusion0 :: Nil )
    val s0b = HOLSequent( f1 :: f2 :: formulas.w1 :: Nil, conclusion0 :: Nil )

    val s1a = HOLSequent( f1 :: f2 :: Nil, conclusion1 :: Nil )
    val s1b = HOLSequent( f1 :: f2 :: formulas.w1 :: Nil, conclusion1 :: Nil )
    val s1c = HOLSequent( f1 :: f2 :: f3 :: f4 :: formulas.w1 :: Nil, conclusion1 :: Nil )
    val s1d = HOLSequent( f1 :: f2 :: f3 :: f4 :: Nil, conclusion1 :: Nil )

    val s2b = HOLSequent( f1 :: f2 :: f4 :: formulas.w2 :: Nil, conclusion2 :: Nil )
    val s2c = HOLSequent( f1 :: f2 :: f4 :: Nil, conclusion2 :: Nil )
    val s2d = HOLSequent( f1 :: f2 :: w3 :: Nil, conclusion2 :: Nil )
    val s2e = HOLSequent( f1 :: f2 :: f3 :: f4 :: w3 :: Nil, conclusion2 :: Nil )

    val consistent = HOLSequent( f1 :: f2 :: f3 :: f4 :: formulas.w1 :: conclusion0 :: Nil, Nil )

    val cuts0a = HOLSequent( f1 :: f2 :: f3 :: f4 :: Nil, formulas.w1 :: Nil )
    val cuts0b = HOLSequent( f3 :: f4 :: formulas.w1 :: Nil, conclusion0 :: Nil )
  }

  import sequents._

  val fn = "ntape6-"

  /**
   * Problem 0: sequence (0,1)
   */
  val p0 = s0a
  /**
   * Problem 1: sequence (1,0,0)
   */
  val p1 = s1a
  /**
   * Problem 0: sequence (1,0,1)
   */
  val p2 = s2c

  /**
   * Problem 0 with witness: sequence (0,1)
   */
  val w0 = s0b
  /**
   * Problem 1 with witness : sequence (1,0,0)
   */
  val w1 = s1c
  /**
   * Problem 2 with witness: sequence (1,0,1)
   */
  val w2 = s2c
  /**
   * Problem 2 with different witness: sequence (1,0,1)
   */
  val w2b = s2e

  /**
   * Export the problems P0-P2 and W0-W2 to TPTP THF.
   *
   * @param path
   */
  def export( path: String = ".", separate_axioms: Boolean = false ) {
    val f = path + File.separator + fn
    //sc
    TPTPHOLExporter( s0a, f + "0-minimal.tptp", separate_axioms ) //provable by agsyhol
    TPTPHOLExporter( s0b, f + "0-with-witness.tptp", separate_axioms ) //provable by agsyhol
    //sc1
    TPTPHOLExporter( s1a, f + "1-minimal.tptp", separate_axioms ) //timeout
    TPTPHOLExporter( s1b, f + "1-withness-no-arith.tptp", separate_axioms ) //timeout
    TPTPHOLExporter( s1c, f + "1-with-witness.tptp", separate_axioms ) //provable by leo 2, satallax, agsyhol
    TPTPHOLExporter( s1d, f + "1-without-witness.tptp", separate_axioms ) //timeout
    //sc2
    TPTPHOLExporter( s2b, f + "2-with-witness.tptp", separate_axioms ) //provable by leo 2, satallax
    TPTPHOLExporter( s2c, f + "2-without-witness.tptp", separate_axioms ) //timeout

    //sc2 with different witness
    TPTPHOLExporter( s2d, f + "2-with-witness2.tptp", separate_axioms ) //provable by leo 2, satallax
    //TPTPHOLExporter(  s2e , f + "2-with-witness2-help.tptp" , separate_axioms ) //provable by leo 2, satallax

    //these are some experiments
    //TPTPHOLExporter(  cuts0a , f + "0-cut1.tptp" , separate_axioms )
    //TPTPHOLExporter(  cuts0b , f + "0-cut2.tptp" , separate_axioms )
    //TPTPHOLExporter(  consistent , f + "0-consistent.tptp" , separate_axioms )
  }
}