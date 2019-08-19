package gapt.examples.tip.axar

import gapt.expr._
import gapt.expr.formula.Formula
import gapt.formats.babel.Notation
import gapt.formats.babel.Precedence
import gapt.proofs.Sequent
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic.Lemma
import gapt.proofs.gaptic.TacticsProof
import gapt.proofs.gaptic._

object prop_01 extends TacticsProof {

  ctx += InductiveType( "nat", hoc"0:nat", hoc"s:nat>nat" )
  ctx += hoc"+:nat>nat>nat"
  ctx += hoc"*:nat>nat>nat"
  ctx += hoc"≤:nat>nat>o"
  ctx += Notation.Infix( "+", Precedence.plusMinus )
  ctx += Notation.Infix( "*", Precedence.timesDiv )
  ctx += Notation.Infix( "≤", Precedence.infixRel )

  val Q: List[Formula] = List(
    hof"!x 0 != s(x)",
    hof"!x !y ( s(x) = s(y) -> x = y )",
    hof"!x (x != 0 -> ?y x = s(y))",
    hof"!x x + 0 = x",
    hof"!x !y x + s(y) = s(x + y)",
    hof"!x x * 0 = 0",
    hof"!x !y x * s(y) = x*y + x",
    hof"!x !y ( x ≤ y <-> ?z z + x = y)" )

  lazy val noind_1 = Lemma(
    Q ++: Sequent() :+ hof"s(s(0)) * s(s(s(0))) + s(s(s(s(s(0))))) = s(s(s(s(s(s(s(s(s(s(s(0)))))))))))" ) {
      rewrite.many ltr "h_6" in "g"
      rewrite ltr "h_5" in "g"
      rewrite.many ltr "h_4" in "g"
      rewrite.many ltr "h_3" in "g"
      refl
    }

  lazy val noind_2 = Lemma(
    Q ++: Sequent() :+ hof"s(s(s(s(s(s(s(s(s(s(0)))))))))) ≤ s(s(0)) * s(s(s(0))) + s(s(s(s(s(0)))))" ) {
      allL( "h_7", le"s(s(s(s(s(s(s(s(s(s(0))))))))))", le"s(s(0)) * s(s(s(0))) + s(s(s(s(s(0)))))" )
      andL( "h_7_0" )
      forget( "h_7_0_0" )
      impL( "h_7_0_1" )
      // 1
      forget( "g" )
      exR( le"s(0)" )
      forget( "h_7_0_1" )
      rewrite.many ltr "h_6" in "h_7_0_1_0"
      rewrite ltr "h_5" in "h_7_0_1_0"
      rewrite.many ltr "h_4" in "h_7_0_1_0"
      rewrite.many ltr "h_3" in "h_7_0_1_0"
      refl
      // 2
      trivial
    }

  lazy val noind_3 = Lemma(
    Q ++: Sequent() :+ hof"?x x*s(s(s(0))) + s(s(s(s(s(0))))) = s(s(s(s(s(s(s(s(s(s(s(0)))))))))))" ) {
      forget( "h_0", "h_1", "h_2", "h_7" )
      exR( le"s(s(0))" )
      forget( "g" )
      rewrite.many ltr "h_6" in "g_0"
      rewrite ltr "h_5" in "g_0"
      rewrite.many ltr "h_4" in "g_0"
      rewrite.many ltr "h_3" in "g_0"
      refl
    }

  lazy val noind_4 = Lemma(
    Q ++: Sequent() :+ hof"?x s(s(s(s(s(s(s(s(s(s(0)))))))))) ≤ s(s(0)) * x + s(s(s(s(s(0)))))" ) {
      forget( "h_0", "h_1", "h_2" )
      exR( le"s(s(s(0)))" )
      forget( "g" )
      allL( "h_7", le"s(s(s(s(s(s(s(s(s(s(0))))))))))", le"s(s(0)) * s(s(s(0))) + s(s(s(s(s(0)))))" )
      forget( "h_7" )
      andL( "h_7_0" )
      forget( "h_7_0_0" )
      impL( "h_7_0_1" )
      // 1
      forget( "g_0" )
      exR( "h_7_0_1", le"s(0)" )
      forget( "h_7_0_1" )
      rewrite.many ltr "h_6" in "h_7_0_1_0"
      rewrite ltr "h_5" in "h_7_0_1_0"
      rewrite.many ltr "h_4" in "h_7_0_1_0"
      rewrite.many ltr "h_3" in "h_7_0_1_0"
      refl
      // 2
      trivial
    }

  lazy val noind_lemma_1 = Lemma( Q ++: Sequent() :+ hof"!x !y (x ≤ y -> s(x) ≤ s(y))" ) {
    decompose
    allL( "h_7", le"s(x)", le"s(y)" )
    andL( "h_7_0" )
    forget( "h_7_0_0" )
    chain( "h_7_0_1" )
    allL( "h_7", le"x:nat", le"y:nat" )
    andL( "h_7_1" )
    forget( "h_7_1_1" )
    impL( "h_7_1_0" )
    trivial
    exL( "h_7_1_0" )
    exR( le"z:nat" )
    escargot
  }

  lazy val openind_1 = Lemma(
    Q ++: Sequent() :+ hof"!x !y !z x + (y + z) = (x + y) + z" ) {
      allR( "g" )
      allR( "g" )
      allR( "g" )
      induction( hov"z:nat" )
      // 1
      rewrite.many ltr "h_3" in "g"
      refl
      // 2
      rewrite.many ltr "h_4" in "g"
      rewrite ltr "IHz_0" in "g"
      refl
    }

  lazy val openind_2 = Lemma(
    Q ++: Sequent() :+ hof"!x !y !z (y + x = z + x -> y = z)" ) {
      allR( "g" )
      allR( "g" )
      allR( "g" )
      induction( hov"x:nat" )
      // 1
      rewrite.many ltr "h_3" in "g"
      impR
      trivial
      // 2
      impR // assume y + s(x) = z + s(x)
      rewrite.many ltr "h_4" in "g_0" // by def of + we have s(y + x) = s(z + x)
      allL( "h_1", le"y + x_0", le"z + x_0" ) // by injectivity of + we have y + x = z + x
      impL( "h_1_0" )
      // 2.1
      trivial
      // 2.2
      impL( "IHx_0" ) // by the induction hypothesis we obtain y = z
      // 2.1
      trivial
      // 2.2
      trivial
    }

  lazy val openind_3a = Lemma( Q ++: Sequent() :+ hof"!x 0 + x = x" ) {
    allR
    induction( hov"x:nat" )
    // 1.1
    rewrite ltr "h_3" in "g"
    refl
    // 1.2
    rewrite ltr "h_4" in "g"
    rewrite ltr "IHx_0" in "g"
    refl
  }

  lazy val openind_3b = Lemma( Q ++: Sequent() :+ hof"!x !y s(x) + y = s(x + y)" ) {
    allR
    allR
    induction( hov"y:nat" )
    // 2.1
    rewrite.many ltr "h_3" in "g"
    refl
    // 2.2
    rewrite.many ltr "h_4" in "g"
    rewrite ltr "IHy_0" in "g"
    refl
  }

  lazy val openind_3 = Lemma( Q ++: Sequent() :+ hof"!x !y x + y = y + x" ) {
    include( "l_1", openind_3a )
    // 2
    include( "l_2", openind_3b )
    // 3
    allR( "g" )
    allR( "g" )
    induction( hov"x:nat" )
    // 3.1
    rewrite ltr "l_1" in "g"
    rewrite ltr "h_3" in "g"
    refl
    // 3.2
    rewrite ltr "l_2" in "g"
    rewrite ltr "h_4" in "g"
    rewrite ltr "IHx_0" in "g"
    refl
  }

  lazy val openind_4 = Lemma( Q ++: Sequent() :+ hof"!x !y !z (x + y = x + z -> y = z)" ) {
    include( "l_1", openind_3 )
    include( "l_2", openind_2 )
    allR( "g" )
    allR( "g" )
    allR( "g" )
    allL( "l_1", le"x:nat", le"y:nat" )
    rewrite ltr "l_1_0" in "g"
    forget( "l_1_0" )
    allL( "l_1", le"x:nat", le"z:nat" )
    rewrite ltr "l_1_0" in "g"
    allL( "l_2", le"x:nat", le"y:nat", le"z:nat" )
    trivial
  }

  lazy val openind_5a = Lemma( Q ++: Sequent() :+ hof"!x !y !z x * (y + z) = x*y + x*z" ) {
    allR
    allR
    allR
    induction( hov"z:nat" )
    escargot
    include( "l_1", openind_1 )
    escargot
  }

  lazy val openind_5 = Lemma( Q ++: Sequent() :+ hof"!x !y !z x * (y * z) = (x * y) * z" ) {
    allR
    allR
    allR
    induction( hov"z:nat" )
    // 1
    rewrite.many ltr "h_5" in "g"
    refl
    // 2
    rewrite.many ltr "h_6" in "g"
    include( "l_1", openind_5a )
    escargot
  }

  lazy val openind_6a = Lemma( Q ++: Sequent() :+ hof"!x 0 * x = 0" ) {
    allR
    induction( hov"x:nat" )
    escargot
    escargot
  }

  lazy val openind_6b = Lemma( Q ++: Sequent() :+ hof"!x !y s(x) * y = x*y + y" ) {
    allR
    allR
    induction( hov"y:nat" )
    rewrite.many ltr "h_5" in "g"
    rewrite ltr "h_3" in "g"
    refl
    rewrite.many ltr "h_6" in "g"
    rewrite.many ltr "h_4" in "g"
    include( "plus_assoc", openind_1 )
    include( "plus_comm", openind_3 )
    escargot
  }

  lazy val openind_6 = Lemma( Q ++: Sequent() :+ hof"!x !y x * y = y * x" ) {
    allR
    allR
    induction( hov"x:nat" )
    include( "l_1", openind_6a )
    escargot
    include( "msl", openind_6b )
    escargot
  }

  lazy val openind_7 = Lemma( Q ++: Sequent() :+ hof"!x !y (x ≤ y | y ≤ x)" ) {
    allR
    allR
    induction( hov"x:nat" )
    // 1
    escargot
    // 2
    orL
    allL( "h_7", le"x_0:nat", le"y:nat" )
    andL
    forget( "h_7_0_1" )
    impL
    trivial
    exL
    allL( "h_2", le"z:nat" )
    impL
    negR
    rewrite ltr "h_2_0" in "h_7_0_0"
    include( "l_1", openind_3a )
    rewrite ltr "l_1" in "h_7_0_0"
    orR
    forget( "g_0" )
    allL( "h_7", le"y:nat", le"s(x_0:nat)" )
    andL
    forget( "h_7_1_0" )
    impL
    forget( "g_1" )
    exR( le"s(0)" )
    forget( "h_7_1_1" )
    include( "l_2", openind_3b )
    rewrite ltr "l_2" in "h_7_1_1_0"
    rewrite ltr "l_1" in "h_7_1_1_0"
    rewrite ltr "h_7_0_0" in "h_7_1_1_0"
    refl
    trivial
    exL
    rewrite ltr "h_2_0" in "h_7_0_0"
    include( "l_1", openind_3b )
    rewrite ltr "l_1" in "h_7_0_0"
    forget( "l_1" )
    rewrite rtl "h_4" in "h_7_0_0"
    forget( "l_1" )
    orR
    forget( "g_1" )
    allL( "h_7", le"s(x_0:nat)", le"y:nat" )
    andL
    forget( "h_7_1_0" )
    impL
    forget( "g_0" )
    exR( le"y_0:nat" )
    trivial
    trivial
    orR
    forget( "g_0" )
    allL( "h_7", le"y:nat", le"x_0:nat" )
    andL
    forget( "h_7_0_1" )
    impL
    trivial
    exL
    allL( "h_7", le"y:nat", le"s(x_0:nat)" )
    andL
    forget( "h_7_1_0" )
    impL
    exR( le"s(z:nat)" )
    include( "l_1", openind_3b )
    rewrite ltr "l_1" in "h_7_1_1_0"
    rewrite ltr "h_7_0_0" in "h_7_1_1_0"
    refl
    trivial
  }

  lazy val openind_8a = Lemma( Q ++: Sequent() :+ hof"!x !y (x != 0 | y != 0 -> x + y != 0)" ) {
    decompose
    orL( "g_0" )
    // case x != 0
    allL( "h_2", le"x:nat" )
    impL( "h_2_0" )
    trivial
    exL
    rewrite ltr "h_2_0" in "g_1"
    include( "l", openind_3b )
    rewrite ltr "l" in "g_1"
    allL( "h_0", le"y_0 + y" )
    negL( "h_0_0" )
    quasiprop
    // case y != 0
    allL( "h_2", le"y:nat" )
    impL( "h_2_0" )
    trivial
    exL
    rewrite ltr "h_2_0" in "g_1"
    rewrite ltr "h_4" in "g_1"
    allL( "h_0", le"x + y_0" )
    negL( "h_0_0" )
    quasiprop
  }

  lazy val openind_8 = Lemma( Q ++: Sequent() :+ hof"∀x ∀y ∀z ( x != 0 ∧ y * x = z * x  →  y = z )" ) {

    cut( "l", hof"!x !y (x ≤ y & x != y -> ?z (z != 0 & z + x = y))" )
    forget( "g" )
    allR
    allR
    impR
    andL
    allL( "h_7", le"x:nat", le"y:nat" )
    andL
    forget( "h_7_0_1" )
    impL
    trivial
    exL
    allL( "h_2", le"z:nat" )
    impL
    negR
    rewrite ltr "h_2_0" in "h_7_0_0"
    include( "l_1", openind_3a )
    rewrite ltr "l_1" in "h_7_0_0"
    negL
    trivial
    exL
    exR( le"z:nat" )
    andR
    negR
    rewrite ltr "l_1_0" in "h_2_0"
    allL( "h_0", le"y_0:nat" )
    negL( "h_0_0" )
    trivial
    trivial

    cut( "f", hof"!x !y !z (x ≤ y & x != y & z != 0 -> x * z ≤ y * z & x * z != y * z)" )
    forget( "g" )
    allR
    allR
    allR
    induction( hov"z:nat" )

    // begin base
    impR
    andL
    andL
    negL( "f_0_1" )
    refl
    // end base

    // begin step

    impR
    andL
    andL

    // begin case distinction on z_0 = 0 | z_0 != 0
    allL( "h_2", le"z_0:nat" )
    impL( "h_2_0" )

    // begin case z_0 = 0
    negR
    rewrite.many ltr "h_2_0" in "f_1"
    rewrite.many ltr "h_6" in "f_1"
    rewrite.many ltr "h_5" in "f_1"
    include( "l_1", openind_3a )
    rewrite.many ltr "l_1" in "f_1"
    prop
    // end case z_0 = 0

    // begin case ?y z_0 = s(y)

    // begin z_0 != 0
    exL( "h_2_0" ) // z_0 = s(y_0)
    cut( "h_2_0_0", hof"z_0 != 0" )
    negR
    rewrite ltr "h_2_0_0" in "h_2_0"
    allL( "h_0", le"y_0:nat" )
    prop
    forget( "h_2_0" )
    //end z_0 != 0

    // begin apply IH
    impL( "IHz_0" )
    andR( "IHz_0" )
    andR( "IHz_0" )
    trivial
    trivial
    trivial
    // end apply IH

    andL( "IHz_0" )

    // begin apply lemma xz_0 < yz_0 -> xz_0 + u = yz_0 for some u != 0
    allL( "l", le"x*z_0", le"y*z_0" )
    impL( "l_0" )
    andR( "l_0" )
    trivial
    trivial
    exL( "l_0", hov"u:nat" )
    andL( "l_0" )
    // end apply lemma xz_0 < yz_0 -> xz_0 + u = yz_0 for some u != 0

    // begin apply lemma x < y -> y = x + v for some v != 0
    allL( "l", le"x:nat", le"y:nat" )
    impL( "l_1" )
    andR( "l_1" )
    trivial
    trivial
    exL( "l_1", hov"v:nat" )
    andL( "l_1" )
    // end apply lemma x < y -> y = x + v for some v != 0

    // begin solve main lemma
    rewrite.many ltr "h_6" in "f_1"
    rewrite.many rtl "l_0_1" in "f_1"
    rewrite.many rtl "l_1_1" in "f_1"
    include( "plus_asso", openind_1 )
    include( "plus_comm", openind_3 )
    include( "lem", openind_8a )
    andR

    // begin <=
    allL( "h_7", le"x * z_0 + x", le"u + (x * z_0) + (v + x)" )
    andL( "h_7_0" )
    forget( "h_7_0_0" )
    impL( "h_7_0_1" )
    exR( "h_7_0_1", le"(u + v)" )
    forget( "h_7_0_1", "f_1", "h_1", "h_2", "h_3", "h_4", "h_5", "h_6", "h_7", "l_1_0", "l_1_1", "l_0_0", "l_0_1", "IHz_0_0", "IHz_0_1", "h_2_0_0", "f_0_0_0", "f_0_0_1", "f_0_1", "l", "h_0", "lem" )
    escargot
    trivial
    // end <=

    // begin !=
    include( "plus_canc", openind_4 )
    allL( "lem", le"u:nat", le"v:nat" )
    forget( "h_7_0_1", "h_1", "h_2", "h_4", "h_5", "h_6", "h_7", "l_1_1", "l_0_1", "IHz_0_0", "IHz_0_1", "h_2_0_0", "f_0_0_0", "f_0_0_1", "f_0_1", "l", "h_0", "lem" )
    allL( "plus_canc", le"x * z_0", le"0", le"u + v" )
    escargot
    // end !=

    // end solve main lemma

    // begin case ?y z_0 = s(y)

    // end step

    // begin apply main lemma
    decompose
    // begin case distinction y <= z | z <= y
    include( "leq_dico", openind_7 )
    allL( "leq_dico", le"y:nat", le"z:nat" )
    allL( "h_7", le"y:nat", le"z:nat" )
    forget( "leq_dico", "l", "h_1", "h_5", "h_6", "h_7" )
    orL

    // begin y <= z
    escargot
    // end y <= z

    // begin z <= y
    escargot
    // end z <= y

    // end case distinction y <= z | z <= y

    // end apply main lemma
  }

  lazy val openind_9a = Lemma( Q ++: Sequent() :+ hof"!x !y (x + y = 0 -> x = 0 & y = 0)" ) {
    decompose
    andR
    allL( "h_2", le"x:nat" )
    impL( "h_2_0" )
    prop
    exL( "h_2_0" )
    rewrite ltr "h_2_0" in "g_0"
    include( "plus_slef", openind_3b )
    escargot
    escargot
  }

  lazy val openind_9 = Lemma( Q ++: Sequent() :+ hof"!x !y ( x ≤ y & y ≤ x -> x = y )" ) {
    decompose
    allL( "h_7", le"x:nat", le"y:nat" )
    allL( "h_7", le"y:nat", le"x:nat" )
    andL( "h_7_0" )
    andL( "h_7_1" )
    forget( "h_7_0_1" )
    forget( "h_7_1_1" )
    impL( "h_7_0_0" )
    trivial
    impL( "h_7_1_0" )
    trivial
    forget( "g_0_0", "g_0_1" )
    include( "plus_canc", openind_4 )
    include( "plus_asso", openind_1 )
    include( "plus_comm", openind_3 )
    forget( "h_7" )
    exL( "h_7_0_0", hov"u:nat" )
    exL( "h_7_1_0", hov"v:nat" )
    rewrite rtl "h_7_0_0" in "h_7_1_0"
    allL( "plus_canc", le"x:nat", le"0", le"u + v" )
    escargot
  }

  ctx += hoc"g:nat>nat"

  lazy val GaussianAxioms = Seq(
    hof"g(0) = 0",
    hof"!x g(s(x)) = g(x) + s(x)" )

  lazy val openind_10 = Lemma( ( Q ++ GaussianAxioms ) ++: Sequent() :+ hof"!x s(s(0)) * g(x) = x * s(x)" ) {
    include( "plus_asso", openind_1 )
    include( "plus_comm", openind_3 )
    include( "mult_comm", openind_6 )
    allR( "g", hov"x:nat" )
    induction( hov"x:nat" )
    escargot
    escargot
  }

  lazy val openind_11a = Q ++: Sequent() :+ hof"!x !y !z ( y ≤ z & y != z -> x + y ≤ x + z & x + y != x + z )"

  lazy val openind_11a_proof = Lemma( openind_11a ) {
    allR
    allR
    allR
    induction( hov"x:nat" )

    // begin base case
    include( "plus_lzer", openind_3a )
    forget( "h_0", "h_1", "h_2", "h_3", "h_4", "h_5", "h_6", "h_7" )
    escargot
    // end base case

    // begin step case
    impR
    andL

    // begin apply the IH
    impL
    prop
    andL
    // end apply the IH

    include( "plus_lsuc", openind_3b )
    rewrite.many ltr "plus_lsuc" in "g_1"
    andR

    // begin sx_0 + y <= sx_0 + z
    include( "leq_succ", noind_lemma_1 )
    chain( "leq_succ" )
    trivial
    // end sx_0 + y <= sx_0 + z

    // begin s(x_0) + y != s(x_0) + z
    allL( "h_1", le"x_0 + y", le"x_0 + z" )
    impL
    prop
    quasiprop
    // end s(x_0) + y != s(x_0) + z

    // end step case
  }

  lazy val openind_11 = Q ++: Sequent() :+ hof"!x !y ( x + x = y + y -> x = y )"

  // via induction with multiplication ( 2*x = 2*y -> x = y ) via lemma above.
  lazy val openind_11_proof_1 = Lemma( openind_11 ) {
    cut( "l", hof"!x x + x = x*s(s(0))" )
    // begin lemma x + x = x*2
    allR( "l" )
    rewrite.many ltr "h_6" in "l"
    rewrite ltr "h_5" in "l"
    include( "plus_lzer", openind_3a )
    rewrite ltr "plus_lzer" in "l"
    refl
    // end lemma
    allR
    allR
    impR
    rewrite.many ltr "l" in "g_0"
    include( "mult_canc", openind_8 )
    allL( "mult_canc", le"s(s(0))", le"x:nat", le"y:nat" )
    impL( "mult_canc_0" )
    andR
    // 2 != 0 via h_0
    allL( "h_0", le"s(0)" )
    quasiprop

    trivial

    trivial
  }

  lazy val openind_lemma_1 = Lemma( Q ++: Sequent() :+ hof"!x !y ( y != 0 -> x + y != x)" ) {
    decompose
    allL( "h_2", le"y:nat" )
    include( "plus_canc", openind_4 )
    forget( "h_2" )
    escargot
  }

  //   via pure s, 0, +, ≤ induction
  lazy val openind_11_proof_2 = Lemma( openind_11 ) {
    allR
    allR
    impR
    include( "leq_dico", openind_7 )
    allL( "leq_dico", le"x:nat", le"y:nat" )
    orL

    // begin x <= y
    allL( "h_7", le"x:nat", le"y:nat" )
    andL( "h_7_0" )
    forget( "h_7_0_1" )
    impL
    trivial
    exL( "h_7_0_0", hov"z:nat" )

    allL( "h_2", le"z:nat" )
    impL( "h_2_0" )

    // begin z_0 = 0
    negR
    rewrite ltr "h_2_0" in "h_7_0_0"
    include( "plus_lzer", openind_3a )
    escargot
    // end z_0 = 0

    // begin z_0 != 0
    cut( "z_ne_zero", hof"z != 0" )
    escargot
    rewrite.many rtl "h_7_0_0" in "g_0"
    include( "plus_comm", openind_3 )
    include( "plus_asso", openind_1 )
    include( "plus_canc", openind_4 )
    escargot
    // end z_0 != 0

    // end x <= y

    // begin y <= x
    allL( "h_7", le"y:nat", le"x:nat" )
    andL( "h_7_0" )
    forget( "h_7_0_1" )
    impL
    trivial
    exL( "h_7_0_0", hov"z:nat" )

    allL( "h_2", le"z:nat" )
    impL( "h_2_0" )

    // begin z_0 = 0
    negR
    rewrite ltr "h_2_0" in "h_7_0_0"
    include( "plus_lzer", openind_3a )
    escargot
    // end z_0 = 0

    // begin z_0 != 0
    cut( "z_ne_zero", hof"z != 0" )
    escargot
    rewrite.many rtl "h_7_0_0" in "g_0"
    include( "plus_comm", openind_3 )
    include( "plus_asso", openind_1 )
    include( "plus_canc", openind_4 )
    forget( "h_2_0", "h_5", "h_6" )
    escargot
    // end z_0 != 0

    // end y <= x
  }

}
