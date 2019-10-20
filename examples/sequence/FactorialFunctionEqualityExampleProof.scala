package sequence

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.Eq
import gapt.expr.formula.Imp
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLFunction
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.fol.Utils
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.macros.ForallLeftBlock
import gapt.proofs.lk.rules.macros.WeakeningLeftMacroRule

/**
 * Proof of f(n) = g(n, 1), where f is the head recursive and
 * g the tail recursive formulation of the factorial function
 */
object FactorialFunctionEqualityExampleProof extends ProofSequence {

  val p = "+"
  val m = "*"
  val s = "s"
  val f = "f"
  val g = "g"

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )
  val z = FOLVar( "z" )

  def f1( sym: String, arg: FOLTerm ) = FOLFunction( sym, arg :: Nil )
  def f2( sym: String, arg1: FOLTerm, arg2: FOLTerm ): FOLTerm = FOLFunction( sym, arg1 :: arg2 :: Nil )
  def f2( arg1: FOLTerm, sym: String, arg2: FOLTerm ): FOLTerm = f2( sym, arg1, arg2 )

  val f_ax_1 = Eq( f1( f, Utils.numeral( 0 ) ), f1( s, Utils.numeral( 0 ) ) )
  val f_ax_2 = fof"!x f(s(x)) = s(x) * f(x)"

  val g_ax_1 = new AllQuantifiedConditionalAxiomHelper( y :: Nil, Nil,
    Eq( y, f2( g, Utils.numeral( 0 ), y ) ) )
  val g_ax_2 = fof"!x!y g(s(x), y) = g(x, y * s(x))"

  val g_compat_2 = new AllQuantifiedConditionalAxiomHelper(
    x :: y :: z :: Nil,
    Eq( y, z ) :: Nil, Eq( f2( g, x, y ), f2( g, x, z ) ) )

  val trans_axiom = new AllQuantifiedConditionalAxiomHelper(
    x :: y :: z :: Nil,
    Eq( x, y ) :: Eq( y, z ) :: Nil, Eq( x, z ) )
  val symm_axiom = All( x, Eq( x, x ) )
  val refl_axiom = new AllQuantifiedConditionalAxiomHelper(
    x :: y :: Nil,
    Eq( x, y ) :: Nil, Eq( y, x ) )
  val compat_mul_axiom = new AllQuantifiedConditionalAxiomHelper(
    x :: y :: z :: Nil,
    Eq( x, y ) :: Nil, Eq( f2( z, m, x ), f2( z, m, y ) ) )
  val assoc_mul_axiom = new AllQuantifiedConditionalAxiomHelper( x :: y :: z :: Nil, Nil,
    Eq( f2( x, m, f2( y, m, z ) ), f2( f2( x, m, y ), m, z ) ) )

  val mul_neutral_axiom = new AllQuantifiedConditionalAxiomHelper( x :: Nil, Nil,
    Eq( f2( x, m, Utils.numeral( 1 ) ), x ) )
  // this second axiom saves us from adding commutativity of multiplication
  val mul_neutral_axiom_2 = new AllQuantifiedConditionalAxiomHelper( x :: Nil, Nil,
    Eq( f2( Utils.numeral( 1 ), m, x ), x ) )

  def apply( n: Int ): LKProof = n match {
    case 0 =>
      val targetEquation = Eq( f1( f, Utils.numeral( 0 ) ), f2( g, Utils.numeral( 0 ), Utils.numeral( 1 ) ) )
      val g0 = Eq( Utils.numeral( 1 ), f2( g, Utils.numeral( 0 ), Utils.numeral( 1 ) ) )
      val ax1 = LogicalAxiom( f_ax_1 )
      val ax2 = LogicalAxiom( g0 )
      val ax3 = LogicalAxiom( targetEquation )
      val p1 = ImpLeftRule( ax2, g0, ax3, targetEquation )
      val p2 = ImpLeftRule( ax1, f_ax_1, p1, Imp( g0, targetEquation ) )
      val p3 = ForallLeftBlock( p2, trans_axiom.getAxiom,
        Seq( f1( f, Utils.numeral( 0 ) ), Utils.numeral( 1 ), f2( g, Utils.numeral( 0 ), Utils.numeral( 1 ) ) ) )
      val p4 = ForallLeftRule( p3, g_ax_1.getAxiom, Utils.numeral( 1 ) )
      WeakeningLeftMacroRule(
        p4,
        List( f_ax_2, g_ax_2, symm_axiom, refl_axiom.getAxiom,
          compat_mul_axiom.getAxiom, assoc_mul_axiom.getAxiom, g_compat_2.getAxiom,
          mul_neutral_axiom.getAxiom, mul_neutral_axiom_2.getAxiom ) )
    case _ => induction_steps( n )
  }

  def induction_steps( n: Int ): LKProof = {
    val axiom = LogicalAxiom( Eq( f1( f, Utils.numeral( n ) ), f2( g, Utils.numeral( n ), Utils.numeral( 1 ) ) ) )

    // add axioms
    val all_axioms = List[FOLFormula]( f_ax_1, f_ax_2, g_ax_1.getAxiom, g_ax_2, symm_axiom, refl_axiom.getAxiom,
      trans_axiom.getAxiom, compat_mul_axiom.getAxiom, assoc_mul_axiom.getAxiom, g_compat_2.getAxiom,
      mul_neutral_axiom.getAxiom, mul_neutral_axiom_2.getAxiom )
    val p1 = all_axioms.foldLeft[LKProof]( axiom )( ( proof, elem ) => WeakeningLeftRule( proof, elem ) )

    val n_num = Utils.numeral( n )

    /**
     * Returns (( ([start_value*]n)*(n-1) ) * ... * ) k
     */
    def get_partial_factorial_term( n: Int, k: Int, start_value: Option[FOLTerm] = None ): FOLTerm = {
      if ( n <= k ) {
        if ( n == k ) {
          start_value match {
            case Some( value ) => f2( value, m, Utils.numeral( n ) )
            case None          => Utils.numeral( n )
          }
        } else throw new Exception( "k larger than n in partial factorial" )
      } else {
        f2( m, get_partial_factorial_term( n, k + 1, start_value ), Utils.numeral( k ) )
      }
    }

    def induction_step_rec( p0: LKProof, k: Int ): LKProof = {

      val k_num = Utils.numeral( k )
      val zero = Utils.numeral( 0 )
      val one = Utils.numeral( 1 )

      val part_fac = if ( n == k ) one else get_partial_factorial_term( n, k + 1 )
      val part_fac_next = get_partial_factorial_term( n, k )

      val f_k_term = if ( n == k ) f1( f, k_num ) // f(k)
      else f2( m, part_fac, f1( f, k_num ) ) // part_fac * f(k)

      val g_k_term = f2( g, k_num, part_fac )

      if ( k == 0 ) {
        // we have: n! * f(0) = g(0, ( ... (( (1 * n) * (n-1) ) * (n-2) ) * ... ) * 1 )

        // use f(0) = s(0)
        val p1 = trans_axiom( List( f_k_term, f2( part_fac, m, f1( s, zero ) ), g_k_term ), p0 )
        val p2 = compat_mul_axiom( List( f1( f, zero ), f1( s, zero ), part_fac ), p1 )
        val p3 = ContractionLeftRule( p2, f_ax_1 )

        // use g(0, y) = y
        val p4 = trans_axiom( List( f2( part_fac, m, f1( s, zero ) ), part_fac, g_k_term ), p3 )
        val p5 = g_ax_1( part_fac :: Nil, p4 )

        // the formula actually says n! * 1 = n!, we have to get rid of the 1
        val p6 = trans_axiom( List( f2( part_fac, m, one ), part_fac, part_fac ), p5 )
        val p7 = mul_neutral_axiom( List( part_fac ), p6 )
        val p8 = ForallLeftRule( p7, symm_axiom, part_fac )
        val p9 = ContractionLeftRule( p8, symm_axiom )

        p9
      } else {
        // lhs contains part_fac * f(k) = g(k, part_fac)

        val km1_num = Utils.numeral( k - 1 ) // must not be evaluated for k == 0
        val f_km1_term = f2( m, part_fac_next, f1( f, km1_num ) ) // (part_fac * k) * f(k-1)
        val g_km1_term = f2( g, km1_num, part_fac_next )

        // first step: decompose f: part_fac * k * f(k-1) = g(k, 1*part_fac)
        val p1 = trans_axiom( List( f_k_term, f_km1_term, g_k_term ), p0 )

        val p3 =
          if ( n == k ) {
            // use axiom directly, part_fac is empty
            val p1_0 = ForallLeftRule( p1, f_ax_2, km1_num )
            ContractionLeftRule( p1_0, f_ax_2 )
          } else {
            // the antecedent contains something along the lines of:
            // 4*f(3) = (4*3) * f(2) or
            // (4*3)*f(2) = ((4*3)*2) * f(1)
            // we however need the last part exposed and grouped to be able
            // to use compat & f_ax2 to show it, like in: 4*f(3) = 4* (3*f(2))
            // use Trans to expose it and show it, other part can be shown by associativity
            // step in between (=yTrans):
            // 4 * (3*f(2)) or
            // (4*3) * (2*f(1))
            val yTrans = f2( part_fac, m, f2( k_num, m, f1( f, km1_num ) ) )
            val p1_0 = trans_axiom( f_k_term :: yTrans :: f_km1_term :: Nil, p1 )
            // show by compat, then f_ax_2: part_fac * f(k) = part_fac * (k * f(k-1))
            val f_k = f1( f, k_num )
            val k_f_km1 = f2( k_num, m, f1( f, km1_num ) )
            val p1_1 = compat_mul_axiom( List( f_k, k_f_km1, part_fac ), p1_0 )
            val p1_2 = ForallLeftRule( p1_1, f_ax_2, km1_num )
            val p1_3 = ContractionLeftRule( p1_2, f_ax_2 )
            // show by assoc: part_fac * (k * f(k-1)) = (part_fac * k) * f(k-1)
            val p1_4 = assoc_mul_axiom( List( part_fac, k_num, f1( f, km1_num ) ), p1_3 )
            p1_4
          }

        // now transform k * f(k-1) = g(k, part_fac) to k * f(k-1) = g(k-1, part_fac * k)
        val p4 = trans_axiom( List( f_km1_term, g_km1_term, g_k_term ), p3 )

        // show g(k, part_fac) = g(k-1, part_fac*k) (need to use reflection to get to this form first)
        val p4_2 = refl_axiom( g_k_term :: g_km1_term :: Nil, p4 )

        val p5 =
          if ( n == k ) {
            // g is initially called with a 1 as second argument, but we want to get rid of it
            // to make the final result equal to the one f produces
            // use trans to split into g-axiom part and part where the two expressions only differ by this extra one
            val g_intermed = f2( g, km1_num, f2( one, m, part_fac_next ) )
            val p5_1 = trans_axiom( g_k_term :: g_intermed :: g_km1_term :: Nil, p4_2 )
            // show g(n, 1) = g(n-1, 1*n) by g_ax_2
            val intermed = All( y, Eq( f2( g, k_num, y ), f2( g, km1_num, f2( y, m, k_num ) ) ) )
            val p5_2 = ForallLeftRule( p5_1, intermed, one )
            val p5_3 = ForallLeftRule( p5_2, g_ax_2, km1_num )
            val p5_4 = ContractionLeftRule( p5_3, g_ax_2 )

            // show g(n-1, 1*n) = g(n-1, n) by g_compat_2
            val p5_5 = g_compat_2( List( km1_num, f2( one, m, k_num ), k_num ), p5_4 )
            // show 1 * k = k
            val p5_6 = mul_neutral_axiom_2( List( k_num ), p5_5 )
            p5_6
          } else {
            val intermed = All( y, Eq(
              f2( g, f1( s, km1_num ), y ),
              f2( g, km1_num, f2( m, y, f1( s, km1_num ) ) ) ) )
            val p6 = ForallLeftRule( p4_2, intermed, part_fac )
            val p7 = ForallLeftRule( p6, g_ax_2, km1_num )
            val p8 = ContractionLeftRule( p7, g_ax_2 )
            p8
          }

        induction_step_rec( p5, k - 1 )
      }
    }

    induction_step_rec( p1, n )
  }
}
