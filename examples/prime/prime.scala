package at.logic.gapt.examples.prime

import at.logic.gapt.examples.TacticsProof
import at.logic.gapt.expr._
import at.logic.gapt.formats.xml.XMLParser.XMLProofDatabaseParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.{ Context, FiniteContext, Sequent }

/**
 * Created by sebastian on 2/25/16.
 */
case class prime( k: Int ) extends TacticsProof {
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
  ctx += "set_1" -> le" λk λl l = k"
  ctx += "ν" -> le" λk λl λm ∃n m = k + n*l"
  ctx += "DIV" -> le" λl λk ∃m l *m = k"
  ctx += "PRIME" -> le" λk (1 < k ∧ ∀l(DIV(l,k) -> (l = 1 ∨ l = k)))"
  ctx += "PRE" -> fof" ∀k (0 < k -> ∃m k = m+1)"
  ctx += "REM" -> hof" ∀l (0 < l -> ∀m∃k (k < l ∧ ν(k,l)(m) ))"
  ctx += "PRIME-DIV" -> hof" ∀m ((¬ m = 1) -> ∃l(PRIME l ∧ DIV l m) )"
  ctx += "subset" -> le" λX λY ∀n (X(n) -> Y(n))"
  ctx += "empty" -> le" λX ¬∃n X(n)"
  ctx += "compN" -> le" λX λx ¬X(x)"
  ctx += "union" -> le" λX λY λx (X(x) ∨ Y(x))"
  ctx += "O" -> le" λX ∀m (X(m) -> ∃l subset(ν(m, l+1), X))"
  ctx += "C" -> le" λX O(compN(X))"
  ctx += "INF" -> le" λX ∀k ∃l X(k+(l + 1))"

  // Definitions that depend on k
  val p = for ( i <- 0 to k )
    yield FOLConst( s"p_$i" )

  p foreach { ctx += _ }

  ctx += ( "P[0]", le" set_1(p_0)" )
  ctx += ( "S[0]", le" ν(0, p_0)" )

  for ( i <- 1 to k ) {
    ctx += ( s"P[$i]", le"union(${P( i - 1 )}, set_1 (${p( i )}:i))" )
    ctx += ( s"S[$i]", le"union(${S( i - 1 )}, ν(0, ${p( i )}))" )
  }

  ctx += ( s"F[$k]", hof" ∀l (PRIME(l) <-> ${P( k )}(l))" )

  // The paper says X = Y <-> X subset Y ∧ Y subset X, but the current proof uses the definition
  // X = Y <-> ∀x (x ∈ X <-> x ∈ Y). Taking the latter for now.
  val extensionality = hof"∀X ∀Y ( (∀x (X(x) <-> Y(x))) -> X = Y )"

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
      unfold( "comp", "compN" )
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
      unfold( "O", "O", "set_1", "ν", "subset" )
      unfold( "C", "O", "set_1", "ν", "subset" )
      trivial
    }

  // Proof that {1} is nonempty
  val singletonNonempty = Lemma(
    Sequent() :+ "nonempty" -> hof" ¬empty(set_1(1))"
  ) {
      unfold( "nonempty", "empty", "set_1" )
      decompose
      exR( "nonempty", hoc" 1:i" )
      trivial
    }

  // Proof that {1} is finite
  val singletonFinite = Lemma(
    ( "infinite" -> hof" INF (set_1 1)" ) +: Sequent()
  ) {
      unfold( "infinite", "INF", "set_1" )
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
      unfold( "CF_0", "ν" )
      exR( "CF_0", fot"n +(k + 1)" )
      forget( "CF_0" )
      axiomTh

      // Right subproof:
      insert( infiniteSubset )
    }

  /**
   * Proof of x ∈ S[n] :- ∃y ( y ∈ P[n] ∧ x ∈ ν(0,y) )
   * @param n
   * @return
   */
  def subProof1( n: Int ): LKProof = {
    require( n <= k )

    val endSequent = ( "Ant" -> hof" ${S( n )}(x)" ) +: Sequent() :+ "Suc" -> hof" ∃y (${P( n )}(y) ∧ ν(0,y)(x))"

    n match {
      case 0 =>
        Lemma( endSequent ) {
          unfold( "Ant", "S[0]" )
          exR( "Suc", p( 0 ) )
          forget( "Suc" )
          andR

          forget( "Ant" )
          unfold( "Suc_0", "P[0]", "set_1" )
          trivial

          unfold( "Ant", "ν" )
          unfold( "Suc_0", "ν" )
          exL( "Ant", fov"x_0" )
          exR( "Suc_0", fov"x_0" )
          trivial
        }

      case _ =>
        val sub1 = Lemma(
          ( "Ant" -> hof" ∃y (${P( n - 1 )}(y) ∧ ν(0,y)(x))" ) +: Sequent() :+ "Suc" -> hof" ∃y (${P( n )}(y) ∧ ν(0,y)(x))"
        ) {
            exL( "Ant", fov" y_0" )
            exR( "Suc", fov" y_0" )
            forget( "Suc" )
            andR( "Suc_0" )

            unfold( "Suc_0", s"P[$n]", "union" )
            decompose
            trivial

            decompose
            trivial
          }

        Lemma(
          endSequent
        ) {
          unfold( "Ant", s"S[$n]", "union" )
          orL( "Ant" )

          cut( "CF", hof" ∃y (${P( n - 1 )}(y) ∧ ν(0,y)(x))" )

          forget( "Suc" )
          insert( subProof1( n - 1 ) )

          insert( sub1 )

          exR( "Suc", p( n ) )
          forget( "Suc" )
          andR( "Suc_0" )

          forget( "Ant" )
          unfold( "Suc_0", s"P[$n]", "union", "set_1" )
          decompose
          trivial

          unfold( "Ant", "ν" )
          unfold( "Suc_0", "ν" )
          exL( "Ant" )
          exR( "Suc_0", fov"n" )
          trivial

        }
    }
  }

  // Proof of F[k] :- x ∈ S[k] -> x ∈ comp({1})
  def subProof2: LKProof = {
    val endSequent = ( "Ant1" -> F( k ).asInstanceOf[HOLFormula] ) +: Sequent() :+ ( "Suc" -> hof" ${S( k )}(x) -> compN(set_1(1))(x) " )

    Lemma( endSequent ) {
      decompose
      unfold( "Suc_1", "compN" )
      cut( "CF", hof"¬x = 1" )

      forget( "Suc_1" )
      cut( "CF2", hof" ∃y (${P( k )}(y) ∧ ν(0,y)(x))" )

      forget( "Ant1", "CF" )
      insert( subProof1( k ) )

      forget( "Suc_0" )
      unfold( "Ant1", s"F[$k]" )
      decompose
      allL( "Ant1", fov"y" )
      decompose
      forget( "Ant1_0_0", "Ant1" )
      impL

      unfold( "CF2_0", s"P[$k]", ( k to 0 by -1 ) map { j => s"P[$j]" }: _* )
      unfold( "CF2_0", "union", "set_1" )
      unfold( "Ant1_0_1", s"P[$k]", ( k to 0 by -1 ) map { j => s"P[$j]" }: _* )
      unfold( "Ant1_0_1", "union", "set_1" )
      prop

      unfold( "Ant1_0_1", "PRIME" )
      decompose
      forget( "Ant1_0_1_1" )
      unfold( "CF2_1", "ν" )
      exL( "CF2_1" )
      paramod( "CF2_1", hoa"0 + n * y = n * y", hof" x = n * y" )
      forget( "CF2_1_cut_0" )
      cut( "CF3", fof" x = 1" )

      trivial

      eqL( "CF3", "CF2_1" )
      forget( "CF3", "CF2_0", "CF" )
      axiomTh

      forget( "Suc_0", "Ant1" )
      unfold( "Suc_1", "set_1" )
      decompose
      trivial
    }
  }
  // Proof of F[k], PRIME-DIV :- S[k] = comp({1}) (under extensionality)
  /*def psi1(k: Int): LKProof = Lemma(
      ("EXT" -> extensionality) +: (s"F[$k]" -> F(k).asInstanceOf[HOLFormula]) +: ("Prime-Div" -> hof" 'PRIME-DIV'") +: Sequent() :+ "goal" -> hof" ${S(k)} = compN(set_1 1)"
    ) {
      chain("EXT")
      forget("EXT")
      allR("goal")
      andR("goal")

      forget("Prime-Div")
      impR("goal")
      unfold("goal_1", "compN")
      cut(hof"¬ x = 1", "CF")

      forget("goal_1")
      cut(hof" ∃(y: i) (in(y, ${P(2)}: i>o) ∧ in(x, ν(0,y)))", "CF2")

      forget(s"F[$k]", "CF")

      /*forget("goal_0", s"F[$k]")
      unfold("goal_1", "set_1", "in")
      trivial*/
    }*/

  def proof( k: Int ): LKProof = {
    require( k >= 0 )
    ???
  }

  def F( k: Int ) = Const( s"F[$k]", To )
  def S( k: Int ) = Const( s"S[$k]", Ti -> To )
  def P( k: Int ) = Const( s"P[$k]", Ti -> To )

  val oldProof = XMLProofDatabaseParser( "examples/prime/ceres_xml/prime1-2.xml.gz" ).proofs( 0 )._2
}

object PrimeProof {
  def main( args: Array[String] ): Unit = {
    val k = args( 0 ).toInt
    prime( k ).subProof2
  }

  val oldProof = XMLProofDatabaseParser( "examples/prime/ceres_xml/prime1-2.xml.gz" ).proofs( 0 )._2
}