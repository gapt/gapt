package gapt.examples.sequence

import gapt.examples.implicationLeftMacro
import gapt.expr.formula.All
import gapt.expr.formula.And
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
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.macros.TransRule

object UniformAssociativity3ExampleProof extends ProofSequence {

  val s = "s"
  val p = "+"

  val x = FOLVar( "x" )
  val y = FOLVar( "y" )
  val z = FOLVar( "z" )

  val x1 = FOLVar( "x_1" )
  val x2 = FOLVar( "x_2" )
  val y1 = FOLVar( "y_1" )
  val y2 = FOLVar( "y_2" )

  def f1( sym: String, arg: FOLTerm ) = FOLFunction( sym, arg :: Nil )
  def f2( sym: String, arg1: FOLTerm, arg2: FOLTerm ): FOLTerm = FOLFunction( sym, arg1 :: arg2 :: Nil )
  def f2( arg1: FOLTerm, sym: String, arg2: FOLTerm ): FOLTerm = f2( sym, arg1, arg2 )

  // Axioms

  // Trans as from TransRule, possibly unify or generalise
  val Trans = All( x, All( y, All( z, Imp( And( Eq( x, y ), Eq( y, z ) ), Eq( x, z ) ) ) ) )
  val Symm = All( x, Eq( x, x ) )
  val Cs = All( x, All( y, Imp( Eq( x, y ), Eq( FOLFunction( s, x :: Nil ), FOLFunction( s, y :: Nil ) ) ) ) )

  // TODO: port these axioms to new format using AllQuantifiedConditionalAxiomHelper
  def refl_ax(): FOLFormula = All( x, refl_ax( x ) )
  def refl_ax( x: FOLTerm ): FOLFormula = All( y, refl_ax( x, y ) )
  def refl_ax( x: FOLTerm, y: FOLTerm ): FOLFormula = Imp( Eq( x, y ), Eq( y, x ) )

  // x=y -> s(x) = s(y)
  def cs_ax(): FOLFormula = All( x, cs_ax( x ) )
  def cs_ax( x: FOLTerm ): FOLFormula = All( y, cs_ax( x, y ) )
  def cs_ax( x: FOLTerm, y: FOLTerm ): FOLFormula =
    Imp( Eq( x, y ), Eq( FOLFunction( s, x :: Nil ), FOLFunction( s, y :: Nil ) ) )

  // x1 = x2 -> y1 = y2 -> x1 + y1 = x2 + y2
  val cp = new AllQuantifiedConditionalAxiomHelper(
    x1 :: x2 :: y1 :: y2 :: Nil,
    Eq( x1, x2 ) :: Eq( y1, y2 ) :: Nil,
    Eq( FOLFunction( p, x1 :: y1 :: Nil ), FOLFunction( p, x2 :: y2 :: Nil ) ) )

  // Arithmetic axioms
  val Ax1 = All( x, Eq( FOLFunction( p, x :: Utils.numeral( 0 ) :: Nil ), x ) )

  // Forall x, y: s(x+y) = x+s(y)
  def ax2_ax(): FOLFormula = All( x, All( y, ax2_ax( x, y ) ) )
  def ax2_ax( x: FOLTerm ): FOLFormula = All( y, ax2_ax( x, y ) )
  def ax2_ax( x: FOLTerm, y: FOLTerm ): FOLFormula =
    Eq( f1( s, f2( x, p, y ) ), f2( x, p, f1( s, y ) ) )

  def addAllAxioms( proof: LKProof ): LKProof =
    Seq( Trans, cp.getAxiom, Symm, ax2_ax(), cs_ax(), refl_ax(), Ax1 ).foldLeft( proof )( WeakeningLeftRule( _, _ ) )

  def apply( n: Int ): LKProof = {
    assert( n >= 0, "n must be >= 0" )
    val proof = if ( n > 0 ) {
      gen_proof_step( 0, n )
    } else {
      val zero = Utils.numeral( 0 )
      val c1 = f2( f2( zero, p, zero ), p, zero )
      val e1 = f2( zero, p, f2( zero, p, zero ) )
      addAllAxioms( LogicalAxiom( Eq( c1, e1 ) ) )
    }
    induction_start( n, proof )
  }

  /**
   * Close off proof ending in (n + n) + 0 = n + (n + 0) |- ...
   */
  def induction_start( n: Int, p0: LKProof ): LKProof = {
    // show both sides equal to n + n
    val n_num = Utils.numeral( n )
    val zero = Utils.numeral( 0 )
    val c1 = f2( f2( n_num, p, n_num ), p, zero )
    val d1 = f2( n_num, p, n_num )
    val e1 = f2( n_num, p, f2( n_num, p, zero ) )
    val p1 = TransRule( c1, d1, e1, p0 )

    // show (n + n) + 0 = (n + n) directly via ax1
    val p2 = ForallLeftRule( p1, Ax1, d1 )
    val p3 = ContractionLeftRule( p2, Ax1 )

    // show (n + n) = n + (n + 0)
    val p4 = cp( n_num :: n_num :: n_num :: f2( n_num, p, zero ) :: Nil, p3 )

    // show n = n and n = n + 0
    val p5 = ForallLeftRule( p4, Symm, n_num )
    val p6 = ContractionLeftRule( p5, Symm )

    val p7 = reflect( f2( n_num, p, zero ), n_num, p6 )

    val p8 = ForallLeftRule( p7, Ax1, n_num )
    ContractionLeftRule( p8, Ax1 )
  }

  /**
   * *
   * Returns proof Pi (currently including line above and below Pi), with numerals n, i, i+1:
   * (n + n) + i+1 = n + (n + i+1), Ax |- ...
   *  Pi
   * (n + n) + i   = n + (n + i), Ax |- ...
   */
  def gen_proof_step( i: Int, n: Int ): LKProof = {
    val n_num = Utils.numeral( n )
    val i_num = Utils.numeral( i )
    val ip1_num = Utils.numeral( i + 1 )

    val a1 = f2( f2( n_num, p, n_num ), p, ip1_num )
    val a2 = f2( n_num, p, f2( n_num, p, ip1_num ) )
    val b1 = f2( n_num, p, f1( s, f2( p, n_num, i_num ) ) )

    val p0 =
      if ( i + 1 >= n ) {
        val final_expression = Eq( a1, a2 )

        val top = LogicalAxiom( final_expression )
        addAllAxioms( top )
      } else {
        gen_proof_step( i + 1, n )
      }

    val p1 = TransRule( a1, b1, a2, p0 )

    // the left side now contains
    // (n + n) + s(i) = n + s(n + i) as well as
    // n + s(n + i) = n + (n + s(i))

    // use Cp to reduce the latter to s(n + i) = (n + s(i))
    val x1_1 = n_num
    val x2_1 = n_num
    val y1_1 = f1( s, f2( n_num, p, i_num ) )
    val y2_1 = f2( n_num, p, f1( s, i_num ) )
    val p8 = cp( x1_1 :: x2_1 :: y1_1 :: y2_1 :: Nil, p1 )

    // show x1 = x2 by symmetry
    val p9 = ForallLeftRule( p8, Symm, n_num )
    val p10 = ContractionLeftRule( p9, Symm )

    // show y1 = y2 by Ax2 (i.e. s(n + i) = (n + s(i)) )
    val p13 = show_by_ax2( n_num, i_num, p10 )

    // now we only have (n + n) + s(i) = n + s(n + i) left (c=e),
    // reduce right hand side by Ax2 and Trans to s(n + (n + i) (c=d) )
    val c1 = f2( f2( n_num, p, n_num ), p, f1( s, i_num ) )
    val d1 = f1( s, f2( n_num, p, f2( n_num, p, i_num ) ) )
    val e1 = f2( n_num, p, f1( s, f2( n_num, p, i_num ) ) )
    val p14 = TransRule( c1, d1, e1, p13 )

    // show d=e by Ax2
    val p15 = show_by_ax2( n_num, f2( n_num, p, i_num ), p14 )

    // next goal: reduce (n + n) + s(i) = s(n + (n + i) to (n + n) + s(i) = s( (n + n) + i) using the IH, Trans and Cs)
    val c2 = f2( f2( n_num, p, n_num ), p, f1( s, i_num ) )
    val d2 = f1( s, f2( f2( n_num, p, n_num ), p, i_num ) )
    val e2 = d1
    val p16 = TransRule( c2, d2, e2, p15 )

    val p17 = show_by_cs( f2( f2( n_num, p, n_num ), p, i_num ), f2( n_num, p, f2( n_num, p, i_num ) ), p16 )

    // now we have:
    // (n + n) + s(i) = s( (n + n) + i)
    // as well as
    // (n + n) + i = n + (n + i)
    // -> use Ax2

    // use reflection to match definition of ax2 afterwards
    val p18 = reflect( d2, c2, p17 )

    val p19 = show_by_ax2( f2( n_num, p, n_num ), i_num, p18 )
    p19

    // we end up with the IH (n + n) + i = n + (n + i)
  }

  def show_by_ax2( x: FOLTerm, y: FOLTerm, p: LKProof ): LKProof = {
    val p1 = ForallLeftRule( p, ax2_ax( x ), y )
    val p2 = ForallLeftRule( p1, ax2_ax(), x )
    ContractionLeftRule( p2, ax2_ax() )
  }

  def show_by_cs( x: FOLTerm, y: FOLTerm, p: LKProof ): LKProof = {
    val p1 = apply_conditional_equality(
      Eq( x, y ) :: Nil,
      Eq( FOLFunction( s, x :: Nil ), FOLFunction( s, y :: Nil ) ), p )

    val p2 = ForallLeftRule( p1, cs_ax( x ), y )
    val p3 = ForallLeftRule( p2, cs_ax(), x )
    ContractionLeftRule( p3, cs_ax() )
  }

  /**
   * Takes a proof s2 with end-sequent of the form
   * (x=y), ... |- ...
   * and return one with end-sequent of the form
   * (y=x), ... |- ...
   */
  def reflect( x: FOLTerm, y: FOLTerm, p: LKProof ): LKProof = {
    val p1 = apply_conditional_equality( Eq( x, y ) :: Nil, Eq( y, x ), p )

    val p2 = ForallLeftRule( p1, refl_ax( x ), y )
    val p3 = ForallLeftRule( p2, refl_ax(), x )
    ContractionLeftRule( p3, refl_ax() )
  }

  private def apply_conditional_equality( equalities: List[FOLFormula], result: FOLFormula, p: LKProof ): LKProof =
    implicationLeftMacro(
      equalities.map { LogicalAxiom },
      equalities.map { e => LogicalAxiom( e ) -> e }.toMap,
      result,
      p )
}
