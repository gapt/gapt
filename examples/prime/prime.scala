package at.logic.gapt.examples.prime

import at.logic.gapt.examples.TacticsProof
import at.logic.gapt.expr._
import at.logic.gapt.formats.xml.XMLParser.XMLProofDatabaseParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs.{ Context, FiniteContext, Sequent }
import at.logic.gapt.prooftool.prooftool

/**
 * Created by sebastian on 2/25/16.
 */
case class prime( k: Int ) extends TacticsProof {
  implicit var ctx = FiniteContext()

  // Types
  ctx += Context.Sort( "i" )

  // Constants
  ctx += Const( "0", Ti )
  ctx += Const( "1", Ti )
  ctx += Const( "+", Ti -> ( Ti -> Ti ) )
  ctx += Const( "*", Ti -> ( Ti -> Ti ) )
  ctx += Const( "<", Ti -> ( Ti -> To ) )
  ctx += Const( "=", Ti -> ( Ti -> To ) )

  //Definitions
  ctx += "set_1" -> le" λk λl l = k"
  ctx += "ν" -> le" λk λl λm ∃n m = k + n*l"
  ctx += "U" -> le" λk λl λm ∃i ((i < l ∧ ¬i = k ) ∧ ν(i,l,m))"
  ctx += "DIV" -> le" λl λk ∃m l *m = k"
  ctx += "PRIME" -> le" λk (1 < k ∧ ∀l(DIV(l,k) -> (l = 1 ∨ l = k)))"
  ctx += "PRE" -> fof" ∀k (0 < k -> ∃m k = m+1)"
  ctx += "REM" -> hof" ∀l (0 < l -> ∀m∃k (k < l ∧ ν(k,l)(m) ))"
  ctx += "PRIME-DIV" -> hof" ∀m ((¬ m = 1) -> ∃l(PRIME l ∧ DIV l m) )"
  ctx += "subset" -> le" λX λY ∀n (X(n) -> Y(n))"
  ctx += "empty" -> le" λX ¬∃n X(n)"
  ctx += "compN" -> le" λX λx ¬X(x)"
  ctx += "union" -> le" λX λY λx (X(x) ∨ Y(x))"
  ctx += "intersection" -> le" λX λY λx (X(x) ∧ Y(x))"
  ctx += "O" -> le" λX ∀m (X(m) -> ∃l subset(ν(m, l+1), X))"
  ctx += "C" -> le" λX O(compN(X))"
  ctx += "INF" -> le" λX ∀k ∃l X(k+(l + 1))"

  // Definitions that depend on k
  val p = for ( i <- 0 to k )
    yield FOLConst( s"p_$i" )

  p foreach {
    ctx += _
  }

  ctx += ( "P[0]", le" set_1(p_0)" )
  ctx += ( "S[0]", le" ν(0, p_0)" )
  ctx += ( "Q[0]", hof" PRIME(${p( 0 )})" )
  ctx += ( "R[0]", hof" ∀y (${P( 0 )}(y) -> PRIME y)" )

  for ( i <- 1 to k ) {
    ctx += ( s"P[$i]", le"union(${P( i - 1 )}, set_1 (${p( i )}:i))" )
    ctx += ( s"S[$i]", le"union(${S( i - 1 )}, ν(0, ${p( i )}))" )
    ctx += ( s"Q[$i]", hof" ${Q( i - 1 )} ∧ PRIME(${p( i )})" )
    ctx += ( s"R[$i]", hof" ∀y (${P( i )} y -> PRIME y)" )
  }

  ctx += ( s"F[$k]", hof" ∀l (PRIME(l) <-> ${P( k )}(l))" )

  // The paper says X = Y <-> X subset Y ∧ Y subset X, but the current proof uses the definition
  // X = Y <-> ∀x (x ∈ X <-> x ∈ Y). Taking the latter for now.
  val extensionality = hof"∀X ∀Y ( (∀x (X(x) <-> Y(x))) -> X = Y )"

  /* -------------
   * | Subproofs |
   * -------------
   */

  val deMorgan1 = Lemma(
    ( "EXT" -> extensionality ) +: Sequent() :+ ( "Suc" -> hof"compN(union X Y) = intersection(compN X)(compN Y)" )
  ) {
      chain( "EXT" )
      forget( "EXT" )
      allR
      repeat( unfold( "compN", "intersection", "union" ) in "Suc" )
      prop

    }

  val intersectionOpen: LKProof = Lemma(
    ( "Ant0" -> hof" O(X)" ) +: ( "Ant1" -> hof" O(Y)" ) +: Sequent() :+ ( "Suc" -> hof" O(intersection X Y)" )
  ) {
      unfold( "O" ) in ( "Ant0", "Ant1", "Suc" )
      allR
      impR
      allL( "Ant0", fov"m" ).forget
      unfold( "intersection" ) in "Suc_0"
      andL
      impL

      trivial

      exL( fov"l_0" )
      allL( "Ant1", fov"m" ).forget
      impL

      trivial

      forget( "Suc_0_0", "Suc_0_1" )
      exL( fov"l_1" )
      exR( fot" (l_0 + 1) * l_1 + l_0" ).forget
      cut( "CF", hoa" (l_0 + 1) * l_1 + l_0 + 1 = (l_0 + 1) * (l_1 + 1)" )

      forget( "Ant0", "Ant1", "Suc_1" )
      axiomTh

      eql( "CF", "Suc_1" )
      forget( "CF" )
      repeat( unfold( "subset", "intersection" ) in "Suc_1" )
      decompose
      andR

      forget( "Ant1" )
      unfold( "subset" ) in ( "Ant0" )
      allL( "Ant0", fov"n" ).forget
      impL

      forget( "Suc_1_1" )
      unfold( "ν" ) in ( "Suc_1_0", "Ant0" )
      exL
      exR( fot"n_0 * (l_1 + 1)" ).forget
      axiomTh

      trivial

      forget( "Ant0" )
      unfold( "subset" ) in ( "Ant1" )
      allL( "Ant1", fov"n" ).forget
      impL

      forget( "Suc_1_1" )
      unfold( "ν" ) in ( "Suc_1_0", "Ant1" )
      exL
      exR( fot"n_0 * (l_0 + 1)" ).forget
      axiomTh

      trivial
    }

  val unionClosed = Lemma(
    ( "Ant0" -> hof"C(X)" ) +: ( "Ant1" -> hof" C(Y)" ) +: ( "EXT" -> extensionality ) +: Sequent() :+ ( "Suc" -> hof" C(union X Y)" )
  ) {
      unfold( "C" ) in ( "Ant0", "Ant1", "Suc" )
      cut( "CF", hof" compN(union X Y) = intersection(compN X)(compN Y)" )

      insert( deMorgan1 )

      eql( "CF", "Suc" )
      forget( "CF" )
      insert( intersectionOpen )
    }

  val progClosed = Lemma(
    ( "PRE" -> hof"PRE" ) +: ( "REM" -> hof"REM" ) +: ( "0<l" -> hof" 0 < l" ) +: ( "EXT" -> extensionality ) +: Sequent() :+ ( "Suc" -> hof"C(ν k l)" )
  ) {
      unfold( "C" ) in "Suc"
      cut( "CF", hof" U(k,l) = compN(ν k l)" )

      forget( "PRE", "Suc" )
      chain( "EXT" )
      forget( "EXT" )
      allR
      andR

      forget( "REM" )
      repeat( unfold( "compN", "U" ) in "CF" )
      decompose
      unfold( "ν" ) in ( "CF_0_1", "CF_1" )
      exL( "CF_0_1" )
      exL( "CF_1" )
      eql( "CF_0_1", "CF_1" )
      forget( "CF_0_1" )
      cut( "tri", fof"i < k ∨ k < i" )

      forget( "CF_0_0_0", "CF_1", "0<l" )
      orR
      axiomTh

      forget( "CF_0_0_1" )
      orL

      axiomTh; axiomTh

      impR
      unfold( "REM" ) in "REM"
      allL( fov"l" ).forget
      impL
      trivial

      forget( "0<l" )
      allL( fov"x" ).forget
      decompose
      unfold( "U" ) in "CF_1"
      exR( fov"k_0" ).forget
      andR

      andR; trivial

      unfold( "compN" ) in "CF_0"
      decompose
      eql( "CF_1", "REM_1" )
      trivial; trivial

      forget( "REM", "EXT" )
      eql( "CF", "Suc" )
      forget( "CF" )
      unfold( "O" ) in "Suc"
      decompose
      unfold( "PRE" ) in "PRE"
      allL( "PRE", fov"l" ).forget
      impL; trivial

      forget( "0<l" )
      exL
      exR( fov"m_0" ).forget
      eql( "PRE", "Suc_1" )
      forget( "PRE" )
      unfold( "subset" ) in "Suc_1"
      unfold( "U" ) in "Suc_0"
      decompose
      unfold( "U" ) in "Suc_1_1"
      exR( fov"i" ).forget
      andR

      andR; trivial; prop

      forget( "Suc_0_0_0", "Suc_0_0_1" )
      unfold( "ν" ) in ( "Suc_0_1", "Suc_1_0", "Suc_1_1" )
      exL( "Suc_0_1" )
      exL( "Suc_1_0" )
      exR( fot"n_0 + n_1" ).forget
      eql( "Suc_0_1", "Suc_1_0" )
      forget( "Suc_0_1" )
      paramod( "Suc_1_0", hoa" (i + n_0 * l) + n_1 *l  = i + (n_0 *l + n_1 * l) ", hof" n = i + (n_0 *l + n_1 * l)" )
      forget( "Suc_1_0_cut_0" )
      paramod( "Suc_1_0", hoa"n_0 * l + n_1 *l = (n_0 + n_1) *l", hof" n = i + (n_0 + n_1) * l" )
      trivial
    }

  // Proof that complement(complement(X)) = X (under extensionality).
  val compCompProof = Lemma(
    ( "EXT" -> extensionality ) +: Sequent() :+ "comp" -> hof" compN(compN(X)) = X"
  ) {
      chain( "EXT" )
      forget( "EXT" )
      allR( "comp", fov"x" )
      unfold( "compN" ) in "comp"
      prop
    }

  // Proof that if complement(X) is closed, X is open (under extensionality).
  val openClosedProof = Lemma(
    ( "EXT" -> extensionality ) +: ( "C" -> hof" C(compN(X))" ) +: Sequent() :+ "O" -> hof"O(X)"
  ) {
      unfold( "C" ) in "C"
      cut( "CF", hof" compN(compN(X)) = X" )

      //Left subproof of the cut:
      forget( "C", "O" )
      insert( compCompProof )

      //Right subproof of the cut:
      forget( "EXT" )

      eql( "CF", "C" ).fromLeftToRight
      forget( "CF" )
      repeat( unfold( "O", "ν", "subset" ) in ( "O", "C" ) )
      trivial
    }

  // Proof that {1} is nonempty
  val singletonNonempty = Lemma(
    Sequent() :+ "nonempty" -> hof" ¬empty(set_1(1))"
  ) {
      repeat( unfold( "empty", "set_1" ) in "nonempty" )
      decompose
      exR( "nonempty", hoc" 1:i" )
      trivial
    }

  // Proof that {1} is finite
  val singletonFinite = Lemma(
    ( "infinite" -> hof" INF (set_1 1)" ) +: Sequent()
  ) {
      repeat( unfold( "INF", "set_1" ) in "infinite" )
      allL( "infinite", hoc"1: i" ).forget
      exL( "infinite" )
      axiomTh
    }

  // Proof of INF(S), S subset X :- INF(X).
  // S and X are free.
  val infiniteSubset = Lemma(
    ( "subset_inf" -> hof"INF(S)" ) +: ( "subset" -> hof" subset S X" ) +: Sequent() :+ "set_inf" -> hof"INF(X)"
  ) {
      unfold( "INF" ) in ( "subset_inf", "set_inf" )
      allR( "set_inf" )
      allL( "subset_inf", fov"k" ).forget
      exL( "subset_inf" )
      exR( "set_inf", fov"l" ).forget
      unfold( "subset" ) in "subset"
      chain( "subset" )
      trivial
    }

  // Proof that every nonempty open set is infinite.
  val phi2 = Lemma(
    ( "open" -> hof" O(X)" ) +: ( "nonempty" -> hof" ¬ empty X" ) +: Sequent() :+ "infinite" -> hof" INF X"
  ) {
      unfold( "empty" ) in "nonempty"
      unfold( "O" ) in "open"
      decompose
      allL( fov"n" ).forget
      impL

      trivial

      forget( "nonempty" )
      exL
      cut( "CF", hof"INF(ν(n, l+1))" )

      // Left subproof: ν(n, l+1) is infinite
      forget( "open", "infinite" )
      unfold( "INF" ) in "CF"
      allR
      exR( fot" n * (l + (1 + 1)) + l * (k+1)" ).forget
      unfold( "ν" ) in "CF"
      exR( fot"n +(k + 1)" ).forget
      axiomTh

      // Right subproof:
      insert( infiniteSubset )
    }

  /**
   * Proof of x ∈ S[n] :- ∃y ( y ∈ P[n] ∧ x ∈ ν(0,y) )
   *
   * @param n
   * @return
   */
  def varrho2( n: Int ): LKProof = {
    val endSequent = ( "Ant" -> hof" ${S( n )}(x)" ) +: Sequent() :+ ( "Suc" -> hof"∃y (${P( n )}(y) ∧ ν 0 y x)" )

    n match {
      case 0 =>
        Lemma( endSequent ) {
          unfold( "S[0]" ) in "Ant"
          exR( p( 0 ) ).forget
          andR

          repeat( unfold( "P[0]", "set_1" ) in "Suc" )
          trivial

          unfold( "ν" ) in ( "Ant", "Suc" )
          exL
          exR( fov"n" ).forget
          trivial
        }

      case _ =>
        Lemma( endSequent ) {
          repeat( unfold( s"S[$n]", "union" ) in "Ant" )
          orL

          cut( "CF", hof"∃y (${P( n - 1 )}(y) ∧ ν 0 y x)" )

          forget( "Suc" )
          insert( varrho2( n - 1 ) )

          forget( "Ant" )
          exL
          exR( fov"y" ).forget
          andR

          repeat( unfold( s"P[$n]", "union", "set_1" ) in "Suc" )
          prop

          andL
          unfold( "ν" ) in ( "CF_1", "Suc" )
          exL
          exR( "Suc", fov"n" ).forget
          trivial

          exR( p( n ) ).forget
          andR

          forget( "Ant" )
          repeat( unfold( s"P[$n]", "union", "set_1" ) in "Suc" )
          orR
          trivial

          repeat( unfold( "ν" ) in ( "Ant", "Suc" ) )
          exL
          exR( "Suc", fov"n" ).forget
          trivial
        }

    }
  }

  // Proof of F[k] :- x ∈ S[k] -> x ∈ comp({1})
  val psi1Left: LKProof = {
    val endSequent = ( "Ant1" -> F( k ).asInstanceOf[HOLFormula] ) +: Sequent() :+ ( "Suc" -> hof" ${S( k )}(x) -> compN(set_1(1))(x) " )

    Lemma( endSequent ) {
      decompose
      unfold( "compN" ) in "Suc_1"
      cut( "CF", hof"¬x = 1" )

      forget( "Suc_1" )
      cut( "CF2", hof" ∃y (${P( k )}(y) ∧ ν(0,y)(x))" )

      forget( "Ant1", "CF" )
      insert( varrho2( k ) )

      forget( "Suc_0" )
      unfold( s"F[$k]" ) in "Ant1"
      decompose
      allL( "Ant1", fov"y" )
      decompose
      forget( "Ant1_0_0", "Ant1" )
      impL

      unfold( s"P[$k]", ( k to 0 by -1 ) map { j => s"P[$j]" }: _* ) in ( "CF2_0", "Ant1_0_1" )
      unfold( "union", "set_1" ) in ( "CF2_0", "Ant1_0_1" )
      prop

      unfold( "PRIME" ) in "Ant1_0_1"
      decompose
      forget( "Ant1_0_1_1" )
      unfold( "ν" ) in "CF2_1"
      exL( "CF2_1" )
      paramod( "CF2_1", hoa"0 + n * y = n * y", hof" x = n * y" )
      forget( "CF2_1_cut_0" )
      cut( "CF3", fof" x = 1" )

      trivial

      eql( "CF3", "CF2_1" )
      forget( "CF3", "CF2_0", "CF" )
      axiomTh

      forget( "Suc_0", "Ant1" )
      unfold( "set_1" ) in "Suc_1"
      decompose
      trivial
    }
  }

  val Pi_1 = Lemma(
    ( "Prime-Div" -> hof" 'PRIME-DIV'" ) +: ( "x!=1" -> hof" ¬x = 1" ) +: ( s"F[$k]" -> hof" ∀l (PRIME(l) <-> X(l))" ) +: Sequent() :+ ( "Suc" -> hof"∃y (X(y) ∧ ν 0 y x)" )
  ) {
      unfold( "PRIME-DIV" ) in "Prime-Div"
      allL( "Prime-Div", fov"x" ).forget
      impL

      trivial

      exL( "Prime-Div" )
      exR( "Suc", fov"l" ).forget
      allL( s"F[$k]", fov"l" ).forget
      decompose
      impL( s"F[$k]_0" )

      trivial

      forget( "Prime-Div_0" )
      andR

      trivial

      forget( s"F[$k]_0" )
      unfold( "DIV" ) in "Prime-Div_1"
      unfold( "ν" ) in "Suc"
      exL
      exR( fov"m" ).forget
      forget( s"F[$k]_1", "x!=1" )
      paramod( "Suc", hoa" 0 + m * l = m * l", hoa"x = m*l" )
      paramod( "Suc", hoa" m * l = l * m", hoa" x = l * m" )
      paramod( "Suc", hoa" l * m = x", hoa" x = x" )
      trivial
    }

  def lambda( n: Int ): LKProof = {
    val endSequent = ( "Ant0" -> hof" ${P( n )}(y)" ) +: ( "Ant1" -> hof" ν 0 y x" ) +: Sequent() :+ "Suc" -> hof" ${S( n )}(x)"

    n match {
      case 0 =>
        Lemma( endSequent ) {
          repeat( unfold( s"P[0]", "set_1" ) in "Ant0" )
          unfold( s"S[0]" ) in "Suc"
          eql( "Ant0", "Suc" )
          trivial
        }

      case _ =>
        Lemma( endSequent ) {
          repeat( unfold( s"P[$n]", s"S[$n]", "union" ) in ( "Ant0", "Suc" ) )
          orR
          orL

          insert( lambda( n - 1 ) )

          unfold( "set_1" ) in "Ant0"
          eql( "Ant0", "Suc_1" )
          trivial
        }
    }
  }

  val psi1Right: LKProof = {
    val endSequent = ( s"F[$k]" -> F( k ).asInstanceOf[HOLFormula] ) +: ( "Prime-Div" -> hof" 'PRIME-DIV'" ) +: Sequent() :+ ( "Suc" -> hof" compN(set_1(1))(x) -> ${S( k )}(x)" )

    Lemma( endSequent ) {
      decompose
      repeat( unfold( "compN", "set_1" ) in "Suc_0" )
      cut( "CF", hof"∃y (${P( k )}(y) ∧ ν 0 y x)" )

      unfold( s"F[$k]" ) in s"F[$k]"
      insert( Pi_1 )

      forget( "Prime-Div", s"F[$k]", "Suc_0" )
      decompose
      insert( lambda( k ) )
    }
  }
  // Proof of EXT, F[k], PRIME-DIV :- S[k] = comp({1})
  def psi1: LKProof = Lemma(
    ( "EXT" -> extensionality ) +: ( s"F[$k]" -> F( k ).asInstanceOf[HOLFormula] ) +: ( "Prime-Div" -> hof" 'PRIME-DIV'" ) +: Sequent() :+ "goal" -> hof" ${S( k )} = compN(set_1 1)"
  ) {
      chain( "EXT" )
      forget( "EXT" )
      allR( "goal" )
      andR( "goal" )

      insert( psi1Left )

      insert( psi1Right )
    }

  def FR: LKProof = Lemma(
    ( "Ant" -> F( k ).asInstanceOf[HOLFormula] ) +: Sequent() :+ ( "Suc" -> R( k ).asInstanceOf[HOLFormula] )
  ) {
      unfold( s"R[$k]" ) in "Suc"
      allR
      unfold( s"F[$k]" ) in "Ant"
      allL( fov" y" )
      andL
      trivial
    }

  def RQ( n: Int ): LKProof = {
    val endSequent = ( "Ant" -> R( n ).asInstanceOf[HOLFormula] ) +: Sequent() :+ ( "Suc" -> Q( n ).asInstanceOf[HOLFormula] )

    n match {
      case 0 =>
        Lemma( endSequent ) {
          unfold( s"Q[0]" ) in "Suc"
          unfold( s"R[0]" ) in "Ant"
          allL( p( 0 ) ).forget
          impL

          repeat( unfold( "P[0]", "set_1" ) in "Ant" )
          trivial

          trivial
        }

      case _ =>
        Lemma( endSequent ) {
          unfold( s"Q[$n]" ) in "Suc"
          cut( s"R[${n - 1}]", R( n - 1 ).asInstanceOf[HOLFormula] )

          //forget( "Suc" )
          unfold( s"R[${n - 1}]" ) in s"R[${n - 1}]"
          allR
          impR
          unfold( s"R[$n]" ) in "Ant"
          allL( fov"y" ).forget
          impL

          repeat( unfold( s"P[$n]", "union" ) in "Ant" )
          prop

          trivial

          //forget( "Ant" )
          andR

          insert( RQ( n - 1 ) )

          forget( s"R[${n - 1}]" )
          unfold( s"R[$n]" ) in "Ant"
          allL( p( n ) ).forget
          impL
          repeat( unfold( s"P[$n]", "union", "set_1" ) in "Ant" )
          orR
          trivial

          trivial
        }
    }
  }

  def FQ: LKProof = Lemma(
    ( "Ant" -> F( k ).asInstanceOf[HOLFormula] ) +: Sequent() :+ ( "Suc" -> Q( k ).asInstanceOf[HOLFormula] )
  ) {
      cut( s"R[$k]", R( k ).asInstanceOf[HOLFormula] )
      insert( FR )
      insert( RQ( k ) )
    }

  def pgt0: LKProof = Lemma(
    ( "Ant" -> fof"PRIME(n)" ) +: Sequent() :+ ( "Suc" -> fof"0 < n" )
  ) {
      cut( "CF", fof" 1 < n" )

      forget( "Suc" )
      unfold( "PRIME" ) in "Ant"
      andL
      trivial

      forget( "Ant" )
      cut( "CF2", fof" 0 + 1 = 1" )

      forget( "CF", "Suc" )
      axiomTh

      eql( "CF2", "CF" )
      forget( "CF2" )
      axiomTh

    }

  def psi2Right( n: Int ): LKProof = {
    val endSequent = ( "EXT" -> extensionality ) +: ( "PRE" -> hof"PRE" ) +: ( s"Q[$n]" -> Q( n ).asInstanceOf[HOLFormula] ) +: ( "REM" -> hof" REM" ) +: Sequent() :+ ( "Suc" -> hof" C ${S( n )}" )

    n match {
      case 0 =>
        Lemma( endSequent ) {
          unfold( "Q[0]" ) in s"Q[$n]"
          cut( "0<p0", fof" 0 < ${p( 0 )}" )

          insert( pgt0 )

          unfold( "S[0]" ) in "Suc"
          insert( progClosed )
        }

      case _ =>
        Lemma( endSequent ) {
          unfold( s"Q[$n]" ) in s"Q[$n]"
          andL
          cut( s"0<p$n", fof" 0 < ${p( n )}" )

          insert( pgt0 )

          unfold( s"S[$n]" ) in "Suc"
          cut( "CF", hof" C(ν 0 ${p( n )})" )

          insert( progClosed )

          cut( "CF2", hof" C(${S( n - 1 )})" )
          insert( psi2Right( n - 1 ) )
          insert( unionClosed )

        }
    }
  }

  def psi2: LKProof = Lemma(
    ( "Ant0" -> hof"${F( k )}" ) +: ( "Ant1" -> hof" REM" ) +: ( "EXT" -> extensionality ) +: ( "PRE" -> hof"PRE" ) +: Sequent() :+ ( "Suc" -> hof" C ${S( k )}" )
  ) {
      cut( s"Q[$k]", Q( k ).asInstanceOf[HOLFormula] )

      insert( FQ )
      insert( psi2Right( k ) )
    }

  def proof: LKProof = {
    val endSequent = ( "EXT" -> extensionality ) +: ( s"F[$k]" -> hof" ${F( k )}" ) +: ( "REM" -> hof" REM" ) +: ( "PRE" -> hof"PRE" ) +: ( "Prime-Div" -> hof" 'PRIME-DIV'" ) +: Sequent()

    Lemma( endSequent ) {
      cut( "INF {1}", hof" INF (set_1 1)" )
      cut( "nonempty {1}", hof" ¬ empty (set_1 1)" )
      insert( singletonNonempty )

      cut( "O {1}", hof" O (set_1 1)" )
      cut( "C compN{1}", hof" C (compN(set_1 1))" )
      cut( "CF", hof" ${S( k )} = compN(set_1 1)" )
      insert( psi1 )

      eql( "CF", "C compN{1}" )
      forget( "CF" )
      insert( psi2 )
      insert( openClosedProof )
      insert( phi2 )

      insert( singletonFinite )
    }
  }

  def F( k: Int ) = Const( s"F[$k]", To )
  def S( k: Int ) = Const( s"S[$k]", Ti -> To )
  def P( k: Int ) = Const( s"P[$k]", Ti -> To )
  def Q( k: Int ) = Const( s"Q[$k]", To )
  def R( k: Int ) = Const( s"R[$k]", To )
}
