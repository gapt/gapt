package at.logic.gapt.examples.prime

import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.LKProof
import at.logic.gapt.proofs._

/**
 * Furstenberg's topological proof of the infinitude of primes.
 *
 * furstenberg(k) proves that there are more than k primes.
 */
case class furstenberg( k: Int ) extends PrimeDefinitions {

  // The paper says X = Y <-> X subset Y ∧ Y subset X, but the current proof uses the definition
  // X = Y <-> ∀x (x ∈ X <-> x ∈ Y). Taking the latter for now.
  ctx += hof"EXT = (∀X ∀Y ((∀x (X x <-> Y x)) -> X = Y))"

  /* -------------
   * | Subproofs |
   * -------------
   */

  val deMorgan1 = Lemma( hols"EXT :- compN(union X Y) = intersection(compN X)(compN Y)" ) {
    unfold( "EXT" ) in "EXT"; chain( "EXT" ); forget( "EXT" )
    allR
    unfold( "compN", "intersection", "union" ) in "g"
    prop
  }

  val intersectionOpen: LKProof = Lemma( hols"O(X), O(Y) :- O(intersection X Y)" ) {
    unfold( "O" ) in ( "h_0", "h_1", "g" )
    allR
    impR
    allL( "h_0", fov"m" ).forget
    unfold( "intersection" ) in "g_0"
    andL
    impL left trivial

    exL( fov"l_0" )
    allL( "h_1", fov"m" ).forget
    impL left trivial

    forget( "g_0_0", "g_0_1" )
    exL( fov"l_1" )
    exR( fot" (l_0 + 1) * l_1 + l_0" ).forget
    cut( "CF", hoa" (l_0 + 1) * l_1 + l_0 + 1 = (l_0 + 1) * (l_1 + 1)" ) left theory

    eql( "CF", "g_1" )
    forget( "CF" )
    unfold( "subset", "intersection" ) in "g_1"
    decompose
    andR

    forget( "h_1" )
    unfold( "subset" ) in "h_0"
    allL( "h_0", fov"n" ).forget
    impL right trivial

    forget( "g_1_1" )
    unfold( "ν" ) in ( "g_1_0", "h_0" )
    exL
    exR( fot"n_0 * (l_1 + 1)" ).forget
    theory

    forget( "h_0" )
    unfold( "subset" ) in "h_1"
    allL( "h_1", fov"n" ).forget
    impL right trivial

    forget( "g_1_1" )
    unfold( "ν" ) in ( "g_1_0", "h_1" )
    exL
    exR( fot"n_0 * (l_0 + 1)" ).forget
    theory
  }

  val unionClosed = Lemma( hols"C(X), C(Y), EXT :- C(union X Y)" ) {
    unfold( "C" ) in ( "h_0", "h_1", "g" )
    cut( "CF", hof" compN(union X Y) = intersection(compN X)(compN Y)" )

    insert( deMorgan1 )

    eql( "CF", "g" )
    forget( "CF" )
    insert( intersectionOpen )
  }

  val progClosed = Lemma( hols"PRE, REM, '0<l': 0 < l, EXT :- C(ν 0 l)" ) {
    unfold( "C" ) in "g"
    cut( "CF", hof" U(0,l) = compN(ν 0 l)" )

    forget( "PRE", "g" )
    unfold( "EXT" ).in( "EXT" ); chain( "EXT" ); forget( "EXT" )
    allR
    andR

    forget( "REM" )
    unfold( "compN", "U" ) in "CF"
    decompose
    unfold( "ν" ) in ( "CF_0_1", "CF_1" )
    exL( "CF_0_1" )
    exL( "CF_1" )
    eql( "CF_0_1", "CF_1" )
    forget( "CF_0_1" )
    cut( "tri", fof"¬0 = i" )

    forget( "CF_0_0_0", "CF_1", "0<l" )
    decompose
    theory

    forget( "CF_0_0_1" )
    decompose
    theory

    impR
    unfold( "REM" ) in "REM"
    allL( fov"l" ).forget
    impL left trivial

    forget( "0<l" )
    allL( fov"x" ).forget
    decompose
    unfold( "U" ) in "CF_1"
    exR( fov"k" ).forget
    andR right trivial

    andR left trivial

    unfold( "compN" ) in "CF_0"
    decompose
    eql( "CF_1", "REM_1" )
    trivial

    forget( "REM", "EXT" )
    eql( "CF", "g" )
    forget( "CF" )
    unfold( "O" ) in "g"
    decompose
    unfold( "PRE" ) in "PRE"
    allL( "PRE", fov"l" ).forget
    impL left trivial

    forget( "0<l" )
    exL
    exR( fov"m_0" ).forget
    rewrite rtl "PRE" in "g_1"
    forget( "PRE" )
    unfold( "subset" ) in "g_1"
    unfold( "U" ) in "g_0"
    decompose
    unfold( "U" ) in "g_1_1"
    exR( fov"i" ).forget
    andR

    andR; trivial; prop

    forget( "g_0_0_0", "g_0_0_1" )
    unfold( "ν" ) in ( "g_0_1", "g_1_0", "g_1_1" )
    decompose
    exR( fot"n_0 + n_1" ).forget
    rewrite.many ltr ( "g_0_1", "g_1_0" )
    theory
  }

  // Proof that complement(complement(X)) = X (under hof"EXT").
  val compCompProof = Lemma( hols"EXT :- comp: compN(compN(X)) = X" ) {
    unfold( "EXT" ) in "EXT"; chain( "EXT" ); forget( "EXT" )
    allR( "comp", fov"x" )
    unfold( "compN" ) in "comp"
    prop
  }

  // Proof that if complement(X) is closed, X is open (under hof"EXT").
  val openClosedProof = Lemma( hols"EXT, C: C(compN(X)) :- O: O(X)" ) {
    unfold( "C" ) in "C"
    cut( "CF", hof" compN(compN(X)) = X" )

    //Left subproof of the cut:
    forget( "C", "O" )
    insert( compCompProof )

    //Right subproof of the cut:
    forget( "EXT" )
    eql( "CF", "C" ).fromLeftToRight
    forget( "CF" )
    unfold( "O", "ν", "subset" ) in ( "O", "C" )
    trivial
  }

  // Proof that {1} is nonempty
  val singletonNonempty = Lemma( hols":- nonempty: ¬empty(set_1(1))" ) {
    unfold( "empty", "set_1" ) in "nonempty"
    decompose
    exR( "nonempty", hoc" 1:i" )
    trivial
  }

  // Proof that {1} is finite
  val singletonFinite = Lemma( hols"infinite: INF (set_1 1) :-" ) {
    unfold( "INF", "set_1" ) in "infinite"
    allL( "infinite", hoc"1: i" ).forget
    exL( "infinite" )
    theory
  }

  // Proof of INF(S), S subset X :- INF(X).
  // S and X are free.
  val infiniteSubset = Lemma( hols"subset_inf: INF(S), subset: subset S X :- set_inf: INF(X)" ) {
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
  val phi2 = Lemma( hols"open: O(X), nonempty: ¬ empty X :- infinite: INF X" ) {
    unfold( "empty" ) in "nonempty"
    unfold( "O" ) in "open"
    decompose
    allL( fov"n" ).forget
    impL left trivial

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
    theory

    // Right subproof:
    insert( infiniteSubset )
  }

  /**
   * Proof of x ∈ S[n] :- ∃y ( y ∈ P[n] ∧ x ∈ ν(0,y) )
   */
  def varrho2( n: Int ): LKProof = {
    val endSequent = hols"${S( n )}(x) :- ∃y (${P( n )}(y) ∧ ν 0 y x)"

    n match {
      case 0 =>
        Lemma( endSequent ) {
          unfold( "S[0]" ) in "h_0"
          exR( p( 0 ) ).forget
          andR

          unfold( "P[0]", "set_1" ) in "g"
          trivial

          unfold( "ν" ) in ( "h_0", "g" )
          exL
          exR( fov"n" ).forget
          trivial
        }

      case _ =>
        Lemma( endSequent ) {
          unfold( s"S[$n]", "union" ) in "h_0"
          orL

          cut( "CF", hof"∃y (${P( n - 1 )}(y) ∧ ν 0 y x)" )

          forget( "g" )
          insert( varrho2( n - 1 ) )

          forget( "h_0" )
          exL
          exR( fov"y" ).forget
          andR

          unfold( s"P[$n]", "union", "set_1" ) in "g"
          prop

          andL
          unfold( "ν" ) in ( "CF_1", "g" )
          exL
          exR( "g", fov"n" ).forget
          trivial

          exR( p( n ) ).forget
          andR

          forget( "h_0" )
          unfold( s"P[$n]", "union", "set_1" ) in "g"
          orR
          trivial

          unfold( "ν" ) in ( "h_0", "g" )
          exL
          exR( "g", fov"n" ).forget
          trivial
        }

    }
  }

  // Proof of F[k] :- x ∈ S[k] -> x ∈ comp({1})
  val psi1Left: LKProof =
    Lemma( hols"h: ${F( k )} :- ${S( k )}(x) -> compN(set_1(1))(x)" ) {
      decompose
      unfold( "compN" ) in "g_1"
      cut( "CF", hof"¬x = 1" )

      forget( "g_1" )
      cut( "CF2", hof" ∃y (${P( k )}(y) ∧ ν(0,y)(x))" )

      forget( "h", "CF" )
      insert( varrho2( k ) )

      forget( "g_0" )
      unfold( s"F[$k]" ) in "h"
      decompose
      allL( "h", fov"y" )
      decompose
      forget( "h_0_0", "h" )
      impL

      unfold( s"P[$k]" +: ( k to 0 by -1 ) map { j => s"P[$j]" }: _* ) in ( "CF2_0", "h_0_1" )
      unfold( "union", "set_1" ) in ( "CF2_0", "h_0_1" )
      prop

      unfold( "PRIME" ) in "h_0_1"
      decompose
      forget( "h_0_1_1" )
      unfold( "ν" ) in "CF2_1"
      decompose
      theory

      unfold( "set_1" ) in "g_1"
      decompose
      trivial
    }

  val Pi_1 = Lemma( hols"'Prime-Div': 'PRIME-DIV', 'x!=1': ¬x = 1, Fk: ∀l (PRIME(l) <-> X(l)) :- ∃y (X(y) ∧ ν 0 y x)" ) {
    unfold( "PRIME-DIV" ) in "Prime-Div"
    allL( "Prime-Div", fov"x" ).forget
    impL left trivial

    exL( "Prime-Div" )
    exR( "g", fov"l" ).forget
    allL( "Fk", fov"l" ).forget
    decompose
    impL( "Fk_0" ) left trivial

    forget( "Prime-Div_0" )
    andR left trivial

    unfold( "DIV" ) in "Prime-Div_1"
    unfold( "ν" ) in "g"
    exL
    exR( fov"m" ).forget
    theory
  }

  def lambda( n: Int ): LKProof = {
    val endSequent = hols"${P( n )}(y), ν 0 y x :- ${S( n )}(x)"

    n match {
      case 0 =>
        Lemma( endSequent ) {
          unfold( s"P[0]", "set_1" ) in "h_0"
          unfold( s"S[0]" ) in "g"
          eql( "h_0", "g" )
          trivial
        }

      case _ =>
        Lemma( endSequent ) {
          unfold( s"P[$n]", s"S[$n]", "union" ) in ( "h_0", "g" )
          orR
          orL left insert( lambda( n - 1 ) )

          unfold( "set_1" ) in "h_0"
          eql( "h_0", "g_1" )
          trivial
        }
    }
  }

  val psi1Right: LKProof =
    Lemma( hols"Fk: ${F( k )}, 'Prime-Div': 'PRIME-DIV' :- compN(set_1(1))(x) -> ${S( k )}(x)" ) {
      decompose
      unfold( "compN", "set_1" ) in "g_0"
      cut( "CF", hof"∃y (${P( k )}(y) ∧ ν 0 y x)" )

      unfold( s"F[$k]" ) in "Fk"
      insert( Pi_1 )

      forget( "Prime-Div", "Fk", "g_0" )
      decompose
      insert( lambda( k ) )
    }
  // Proof of EXT, F[k], PRIME-DIV :- S[k] = comp({1})
  val psi1: LKProof = Lemma( hols"EXT, Fk: ${F( k )}, 'Prime-Div': 'PRIME-DIV' :- ${S( k )} = compN(set_1 1)" ) {
    unfold( "EXT" ) in "EXT"; chain( "EXT" ); forget( "EXT" )
    allR( "g" )
    andR( "g" )

    insert( psi1Left )

    insert( psi1Right )
  }

  val FR: LKProof = Lemma( hols"Fk: ${F( k )} :- Rk: ${R( k )}" ) {
    unfold( s"R[$k]" ) in "Rk"
    allR
    unfold( s"F[$k]" ) in "Fk"
    allL( fov" y" )
    andL
    trivial
  }

  def RQ( n: Int ): LKProof = {
    val endSequent = hols"Rn: ${R( n )} :- Qn: ${Q( n )}"

    n match {
      case 0 =>
        Lemma( endSequent ) {
          unfold( s"Q[0]" ) in "Qn"
          unfold( s"R[0]" ) in "Rn"
          allL( p( 0 ) ).forget
          impL right trivial

          unfold( "P[0]", "set_1" ) in "Rn"
          trivial
        }

      case _ =>
        Lemma( endSequent ) {
          unfold( s"Q[$n]" ) in "Qn"
          cut( "Rn1", R( n - 1 ).asInstanceOf[Formula] )

          //forget( "Suc" )
          unfold( s"R[${n - 1}]" ) in "Rn1"
          allR
          impR
          unfold( s"R[$n]" ) in "Rn"
          allL( fov"y" ).forget
          impL right trivial

          unfold( s"P[$n]", "union" ) in "Rn"
          prop

          andR

          insert( RQ( n - 1 ) )

          forget( "Rn1" )
          unfold( s"R[$n]" ) in "Rn"
          allL( p( n ) ).forget
          impL right trivial

          unfold( s"P[$n]", "union", "set_1" ) in "Rn"
          orR
          trivial
        }
    }
  }

  val FQ: LKProof = Lemma( hols"${F( k )} :- ${Q( k )}" ) {
    cut( s"Rk", R( k ).asInstanceOf[Formula] )
    insert( FR )
    insert( RQ( k ) )
  }

  val pgt0: LKProof = Lemma( hols"prime: PRIME(n) :- pos: 0 < n" ) {
    cut( "CF", fof" 1 < n" )

    forget( "pos" )
    unfold( "PRIME" ) in "prime"
    andL
    trivial

    forget( "prime" )
    cut( "CF2", fof" 0 + 1 = 1" )

    theory

    eql( "CF2", "CF" )
    theory

  }

  def psi2Right( n: Int ): LKProof = {
    val endSequent = hols"EXT, PRE, Qn: ${Q( n )}, REM :- C: C ${S( n )}"

    n match {
      case 0 =>
        Lemma( endSequent ) {
          unfold( "Q[0]" ) in "Qn"
          cut( "0<p0", fof" 0 < ${p( 0 )}" )

          insert( pgt0 )

          unfold( "S[0]" ) in "C"
          insert( progClosed )
        }

      case _ =>
        Lemma( endSequent ) {
          unfold( s"Q[$n]" ) in "Qn"
          andL
          cut( s"0<p$n", fof" 0 < ${p( n )}" )

          insert( pgt0 )

          unfold( s"S[$n]" ) in "C"
          cut( "CF", hof" C(ν 0 ${p( n )})" )

          insert( progClosed )

          cut( "CF2", hof" C(${S( n - 1 )})" )
          insert( psi2Right( n - 1 ) )
          insert( unionClosed )
        }
    }
  }

  val psi2: LKProof = Lemma( hols"${F( k )}, REM, EXT, PRE :- C ${S( k )}" ) {
    cut( s"Q[$k]", Q( k ).asInstanceOf[Formula] )

    insert( FQ )
    insert( psi2Right( k ) )
  }

  val proof: LKProof =
    Lemma( hols"EXT, ${F( k )}, REM, PRE, 'PRIME-DIV' :-" ) {
      cut( "INF {1}", hof" INF (set_1 1)" ) right insert( singletonFinite )
      cut( "nonempty {1}", hof" ¬ empty (set_1 1)" )
      insert( singletonNonempty )

      cut( "O {1}", hof" O (set_1 1)" ) right insert( phi2 )
      cut( "C compN{1}", hof" C (compN(set_1 1))" ) right insert( openClosedProof )
      cut( "CF", hof" ${S( k )} = compN(set_1 1)" )
      insert( psi1 )

      eql( "CF", "C compN{1}" )
      forget( "CF" )
      insert( psi2 )
    }
}
object furstenberg3 extends furstenberg( 3 )
