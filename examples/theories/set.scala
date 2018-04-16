package gapt.examples.theories

import gapt.expr._
import gapt.formats.babel.Precedence
import gapt.proofs.gaptic._

object set extends Theory( logic ) {
  dfn( hof" empty{?a} = (λ(x:?a) false)" )
  dfn( hof" univ{?a} = (λ(x:?a) true)" )
  dfn( hof" subset{?a} (P: ?a > o) (Q: ?a > o) = (∀x (P(x) -> Q(x)))" )
  dfn( hof" union{?a} (P: ?a > o) (Q: ?a > o) = (λx P(x) ∨ Q(x))" )
  dfn( hof" intersect{?a} (P: ?a > o) (Q: ?a > o) = (λx P(x) ∧ Q(x))" )
  dfn( hof" comp{?a} (P: ?a > o) = (λx ¬ P(x))" )
  dfn( hof" setminus{?a} (P: ?a > o) (Q: ?a > o) = (intersect P (comp Q))" )
  dfn( hof" insert{?a} (P: ?a > o) (x: ?a) = (λy (P(y) ∨ y = x))" )
  dfn( hof" pairset{?a} (x: ?a) (y: ?a) = insert (insert empty x) y" )
  dfn( hof" bigunion{?a} (P: (?a > o) > o) = (λx ∃X (P(X) ∧ X(x)))" )
  dfn( hof" bigintersect{?a} (P: (?a > o) > o) = (λx ∀X (P(X) -> X(x)))" )
  dfn( hof" preimg{?a ?b} (f: ?a > ?b) (X: ?b > o) = (λx X (f x))" )

  attr( "simp" )(
    "empty",
    "univ",
    "union",
    "intersect",
    "comp",
    "setminus",
    "pairset",
    "bigunion",
    "bigintersect",
    "insert" )

  infix( "∩", Precedence.timesDiv, const = "intersect" )
  infix( "∪", Precedence.plusMinus, const = "union" )
  infix( "⊂", Precedence.infixRel, const = "subset" )

  val extAxiom = lemma( hof"X = Y <-> ∀x (X(x) <-> Y(x))" ) { simp.w( "funextiff", "propextiff" ) }

  val compComp = lemma( hof"comp(comp(X)) = X", "simp" ) { simp.w( "extAxiom", "comp" ) }

  val subsetRefl = lemma( hof" X ⊂ X", "simp" ) { simp.w( "subset" ) }

  val subsetTrans = lemma( hof" ((X ⊂ Y) ∧ (Y ⊂ Z)) -> X ⊂ Z" ) {
    simp.w( "subset" )
    escrgt
  }

  val eqSubset = lemma( hof" X = Y <-> ((X ⊂ Y) ∧ (Y ⊂ X))" ) {
    simp.w( "extAxiom", "subset" )
    escrgt
  }

  val emptyUnique = lemma( hof"∀(x: ?a) ¬ X(x) -> X = empty" ) {
    simp.w( "extAxiom" )
  }

  val univUnique = lemma( hof"∀(x: ?a) X(x) -> X = univ" ) {
    simp.w( "extAxiom" )
  }

  val emptyComp = lemma( hof" comp(empty) = univ", "simp" ) {
    simp.w( "extAxiom" )
  }

  val emptySubset = lemma( hof"empty ⊂ X", "simp" ) {
    simp.w( "subset" )
  }

  val subsetUniv = lemma( hof" X ⊂ univ", "simp" ) {
    simp.w( "subset" )
  }

  val unionUnion = lemma( hof"X ∪ X = X", "simp" ) {
    simp.w( "extAxiom" )
    allR
    prop
  }

  val unionAssoc = lemma( hof" X ∪ (Y ∪ Z) = (X ∪ Y) ∪ Z" ) {
    simp.w( "extAxiom" )
    allR
    prop
  }

  val unionComm = lemma( hof"X ∪ Y = Y ∪ X" ) {
    simp.w( "extAxiom" )
    allR
    prop
  }

  val subsetUnion = lemma( hof" X ∪ Y = Y <-> X ⊂ Y" ) {
    simp.w( "subset", "extAxiom" )
    escrgt
  }

  val unionSubset1 = lemma( hof" X ⊂ (X ∪ Y)", "simp" ) {
    simp.w( "subset" )
    allR
    prop
  }

  val unionSubset2 = lemma( hof" Y ⊂ (X ∪ Y)", "simp" ) {
    simp.w( "subset" )
    allR
    prop
  }

  val subsetIntersect = lemma( hof" X ∩ Y = X <-> X ⊂ Y" ) {
    simp.w( "subset", "extAxiom" )
    escrgt
  }

  val intersectIntersect = lemma( hof"X ∩ X = X", "simp" ) {
    simp.w( "extAxiom" )
    allR
    prop
  }

  val intersectAssoc = lemma( hof" X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z" ) {
    simp.w( "extAxiom" )
    allR
    prop
  }

  val intersectComm = lemma( hof" X ∩ Y = Y ∩ X" ) {
    simp.w( "extAxiom" )
    allR
    prop
  }

  val intersectSubset1 = lemma( hof" (X ∩ Y) ⊂ X" ) {
    simp.w( "subset" )
    allR
    prop
  }

  val intersectSubset2 = lemma( hof" (X ∩ Y) ⊂ Y" ) {
    simp.w( "subset" )
    allR
    prop
  }

  val univUnion1 = lemma( hof" X ∪ univ = univ", "simp" ) {
    simp.w( "subsetUnion" )
  }

  val univUnion2 = lemma( hof" univ ∪ X = univ", "simp" ) {
    include( "unionComm" )
    rewrite ltr "unionComm" in "g"
    simp
  }

  val univIntersect1 = lemma( hof" X ∩ univ = X", "simp" ) {
    simp.w( "subsetIntersect" )
  }

  val univIntersect2 = lemma( hof" univ ∩ X = X", "simp" ) {
    include( "intersectComm" )
    rewrite ltr "intersectComm" in "g"
    simp
  }

  val emptyUnion1 = lemma( hof" X ∪ empty = X", "simp" ) {
    include( "unionComm" )
    rewrite ltr "unionComm" in "g"
    simp.w( "subsetUnion" )
  }

  val emptyUnion2 = lemma( hof" empty ∪ X = X", "simp" ) {
    simp.w( "subsetUnion" )
  }

  val emptyIntersect1 = lemma( hof" X ∩ empty = empty", "simp" ) {
    include( "intersectComm" )
    rewrite ltr "intersectComm" in "g"
    simp.w( "subsetIntersect" )
  }

  val emptyIntersect2 = lemma( hof" empty ∩ X = empty", "simp" ) {
    simp.w( "subsetIntersect" )
  }
  val deMorgan1 = lemma( hof"comp(X ∪ Y) = comp(X) ∩ comp(Y)" ) { simp.w( "extAxiom" ) }

  val deMorgan2 = lemma( hof" comp(X ∩ Y) = comp(X) ∪ comp(Y)" ) { simp.w( "extAxiom" ) }

  val unionIntersectDistrib = lemma( hof" (X ∪ Y) ∩ Z = (X ∩ Z) ∪ (Y ∩ Z)" ) {
    simp.w( "extAxiom" )
    escrgt
  }

  val intersectUnionDistrib = lemma( hof" (X ∩ Y) ∪ Z = (X ∪ Z) ∩ (Y ∪ Z)" ) {
    simp.w( "extAxiom" )
    escrgt
  }

  val insertUniv = lemma( hof" insert univ x = univ", "simp" ) {
    simp.w( "extAxiom" )
  }

  val insertUnion = lemma( hof" bigunion (insert P x) = (bigunion P) ∪ x" ) {
    simp.w( "extAxiom" )
    escrgt
  }

  val insertIntersect = lemma( hof" bigintersect (insert P x) = (bigintersect P) ∩ x" ) {
    simp.w( "extAxiom" )
    escrgt
  }

  val insertSubset = lemma( hof" X ⊂ insert X x", "simp" ) {
    simp.w( "subset" )
    escrgt
  }

  val insertElement = lemma( hof" (insert X x) x", "simp" ) {
    simp
  }

  val pairsetUnion = lemma( hof" bigunion (pairset X Y) = X ∪ Y", "simp" ) {
    simp.w( "extAxiom" )
    escrgt
  }

  val pairsetIntersect = lemma( hof" bigintersect (pairset X Y) = X ∩ Y", "simp" ) {
    simp.w( "extAxiom" )
    escrgt
  }

  val bigunionEmpty = lemma( hof" bigunion empty = empty", "simp" ) {
    simp.w( "extAxiom" )
  }

  val bigintersectEmpty = lemma( hof" bigintersect empty = univ", "simp" ) {
    simp.w( "extAxiom" )
  }

  val pairsetElem1 = lemma( hof" (pairset x y) x", "simp" ) {
    simp
  }

  val pairsetElem2 = lemma( hof"(pairset x y) y", "simp" ) {
    simp
  }

  val preimgIntersect = lemma( hof" preimg f (X ∩ Y) = (preimg f X) ∩ (preimg f Y)" ) {
    simp.w( "extAxiom", "preimg" )
  }

  val preimgUnion = lemma( hof" preimg f (X ∪ Y) = (preimg f X) ∪ (preimg f Y)" ) {
    simp.w( "extAxiom", "preimg" )
  }

  val preimgEmpty = lemma( hof" preimg f empty = empty", "simp" ) {
    simp.w( "preimg", "extAxiom" )
  }
  val preimgUniv = lemma( hof" preimg f univ = univ", "simp" ) {
    simp.w( "preimg", "extAxiom" )
  }
}