import at.logic.gapt.examples.TacticsProof
import at.logic.gapt.expr._
import at.logic.gapt.formats.xml.XMLParser.XMLProofDatabaseParser
import at.logic.gapt.proofs.Context._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.{ Sequent, Context, FiniteContext }

/**
 * Created by sebastian on 2/25/16.
 */
object prime extends TacticsProof {
  implicit var ctx = FiniteContext()

  // Types
  ctx += Context.Sort( "i" )

  // Constants
  ctx += hoc" 0: i"
  ctx += hoc" 1: i"
  ctx += hoc" '+': i > i > i"
  ctx += hoc" '*': i > i > i"
  ctx += hoc" '<': i > i > o"
  ctx += hoc" '=': i > i > o"

  //Definitions
  ctx += "set_1" -> le" λk λl k = l"
  ctx += "in" -> le" λ(x: i) λ(X: i > o) X(x)"
  ctx += "ν" -> le" λk λl λm ∃n m = k + n*l"
  ctx += "DIV" -> le" λl λk ∃m l *m = k"
  ctx += "PRIME" -> le" λk (1 < k ∧ ∀l(DIV(l,k) -> (l = 1 ∨ l = k)))"
  ctx += "PRE" -> fof" ∀k (0 < k -> ∃m k = m+1)"
  ctx += "REM" -> hof" ∀l (0 < l -> ∀m∃k (k < l ∧ in(m, ν(k,l))) )"
  ctx += "PRIME-DIV" -> hof" ∀m ((¬ m = 1) -> ∃l(PRIME l ∧ DIV l m) )"
  ctx += "subset" -> le" λX λY ∀n (in(n, X) -> in(n, Y))"
  ctx += "empty" -> le" (λX ¬∃n in n X): (i > o) > o"
  ctx += "compN" -> le" (λX λx ¬X(x)): (i >o) > (i > o)"
  ctx += "union" -> le" λX λY λx (in(x, X) ∨ in(x,Y))"
  ctx += "O" -> le" (λX ∀m (in m X -> ∃l subset(ν(m, l+1), X))): (i > o) > o"
  ctx += "C" -> le" (λ(X: i > o) O(compN(X))): (i > o) > o"
  ctx += "INF" -> le" (λX ∀k ∃l in(k+(l + 1), X)): (i > o) > o"

  // save the current "base" context, i.e. everything that does not depend on k
  val baseCTX = ctx

  // The paper says X = Y <-> X subset Y ∧ Y subset X, but the current proof uses the definition
  // X = Y <-> ∀x (x ∈ X <-> x ∈ Y). Taking the latter for now.
  val extensionality = hof"∀X ∀Y ( ∀x (in(x,X) <-> in(x,Y)) -> X = Y)"

  /* -------------
   * | Subproofs |
   * -------------
   */

  // Proof that complement(complement(X)) = X (under extensionality).
  val compCompProof = Lemma(
    ( "EXT" -> extensionality ) +: Sequent() :+ "comp" -> hof" compN(compN(X)) = X"
  ) {
      chain( "EXT" )
      forget( "EXT" )
      allR( "comp", fov"x" )
      unfold( "comp", "compN", "set_1", "in" )
      prop
    }

  // Proof that if complement{1} is closed, {1} is open (under extensionality).
  val openClosedProof = Lemma(
    ( "EXT" -> extensionality ) +: ( "C" -> hof" C(compN(set_1(1)))" ) +: Sequent() :+ "O" -> hof"O(set_1(1))"
  ) {
      unfold( "C", "C" )
      cut( "CF", hof" compN(compN(set_1 1)) = set_1 1" )

      //Left subproof of the cut:
      forget( "C", "O" )
      insert( compCompProof )

      //Right subproof of the cut:
      forget( "EXT" )
      unfold( "C", "C" )
      eqL( "CF", "C" ).fromLeftToRight
      forget( "CF" )
      unfold( "O", "O", "set_1", "ν", "subset", "in" )
      unfold( "C", "O", "set_1", "ν", "subset", "in" )
      trivial
    }

  // Proof that {1} is nonempty
  val singletonNonempty = Lemma(
    Sequent() :+ "nonempty" -> hof" ¬empty(set_1(1))"
  ) {
      unfold( "nonempty", "empty", "set_1", "in" )
      decompose
      exR( "nonempty", hoc" 1:i" )
      trivial
    }

  // Proof that {1} is finite
  val singletonFinite = Lemma(
    ( "infinite" -> hof" INF (set_1 1)" ) +: Sequent()
  ) {
      unfold( "infinite", "INF", "set_1", "in" )
      allL( "infinite", hoc"1: i" )
      forget( "infinite" )
      exL( "infinite_0" )
      axiomTh
    }

  // Proof of INF(S), S subset X :- INF(X).
  // S and X are free.
  val infiniteSubset = Lemma(
    ( "subset_inf" -> hof"INF(S)" ) +: ( "subset" -> hof" subset S X" ) +: Sequent() :+ "set_inf" -> hof"INF(X)"
  ) {
      unfold( "subset_inf", "INF" )
      unfold( "set_inf", "INF" )
      allR( "set_inf" )
      allL( "subset_inf", fov"k" )
      exL( "subset_inf_0" )
      exR( "set_inf", fov"l" )
      forget( "set_inf", "subset_inf" )
      unfold( "subset", "subset" )
      chain( "subset" )
      trivial //If we don't need to unfold ∈.
    }

  // Proof that every nonempty open set is infinite.
  val phi2 = Lemma(
    Sequent() :+ "goal" -> hof"∀X ((O(X) ∧ ¬ empty(X)) -> INF(X))"
  ) {
      decompose
      unfold( "goal_0_1", "empty" )
      decompose
      unfold( "goal_0_0", "O" )
      decompose
      allL( "goal_0_0", fov"n" )
      forget( "goal_0_0" )
      impL( "goal_0_0_0" )

      trivial // n ∈ X :- n ∈ X -- do we need to expand this further?

      forget( "goal_0_1" )
      exL( "goal_0_0_0" )
      cut( "CF", hof"INF(ν(n, l+1))" )

      // Left subproof: ν(n, l+1) is infinite
      forget( "goal_0_0_0", "goal_1" )
      unfold( "CF", "INF" )
      allR( "CF" )
      exR( "CF", fot" n * (l + (1 + 1)) + l * (k+1)" )
      forget( "CF" )
      unfold( "CF_0", "ν", "in" )
      exR( "CF_0", fot"n +(k + 1)" )
      forget( "CF_0" )
      axiomTh

      // Right subproof:
      insert( infiniteSubset )
    }

  def updateContext( k: Int ): Unit = {
    require( k >= 0 )

    ctx = baseCTX

    val p = for ( i <- 0 to k )
      yield FOLConst( s"p_$i" )

    p foreach { ctx += _ }

    ctx += ( "P[0]", le" set_1(p_0)" )
    ctx += ( "S[0]", le" ν(0, p_0)" )

    for ( i <- 1 to k ) {
      ctx += ( s"P[$i]", le"union(${P( i - 1 )}: i > o, set_1 (${p( i )}:i))" )
      ctx += ( s"S[$i]", le"union(${P( i - 1 )}: i > o, ν(0, ${p( i )}))" )
    }

    ctx += ( s"F[$k]", hof" ∀l (PRIME(l) <-> in(l, ${P( k )}))" )
  }

  // Proof of F[k], PRIME-DIV :- S[k] = comp({1}) (under extensionality)
  def psi1( k: Int ): LKProof = {
    updateContext( k )

    Lemma(
      ( "EXT" -> extensionality ) +: ( s"F[$k]" -> F( k ).asInstanceOf[HOLFormula] ) +: ( "Prime-Div" -> hof" 'PRIME-DIV'" ) +: Sequent() :+ "goal" -> hof" ${S( k )} = compN(set_1 1)"
    ) {
        chain( "EXT" )
        forget( "EXT" )
        allR( "goal" )
        andR( "goal" )
      }
  }

  def proof( k: Int ): LKProof = {
    require( k >= 0 )

    updateContext( k )

    ???
  }

  def F( k: Int ) = Const( s"F[$k]", To )
  def S( k: Int ) = Const( s"S[$k]", Ti -> To )
  def P( k: Int ) = Const( s"P[$k]", Ti -> To )

  val oldProof = XMLProofDatabaseParser( "examples/prime/ceres_xml/prime1-2.xml.gz" ).proofs( 0 )._2
}