import at.logic.gapt.expr._
import at.logic.gapt.examples.theories.{ Theory, logic }
import at.logic.gapt.formats.babel.Precedence
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.prooftool.prooftool

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

  val extAxiom = axiom( hof" ∀(X: ?a > o) ∀(Y: ?a > o) (X = Y <-> ∀(x: ?a) (X(x) <-> Y(x)))" )

  val compcomp = lemma( hof"comp(comp(X)) = X", "simp" ) { simp.w( "extAxiom", "comp" ) }

  val subsetrefl = lemma( hof" X ⊂ X", "simp" ) { simp.w( "subset" ) }

  val subsettrans = lemma( hof" ((X ⊂ Y) ∧ (Y ⊂ Z)) -> X ⊂ Z" ) {
    simp.w( "subset" )
    escrgt
  }

  val eqsubset = lemma( hof" X = Y <-> ((X ⊂ Y) ∧ (Y ⊂ X))" ) {
    simp.w( "extAxiom", "subset" )
    escrgt
  }

  val emptyunique = lemma( hof"∀(x: ?a) ¬ X(x) -> X = empty" ) {
    simp.w( "extAxiom" )
  }

  val univunique = lemma( hof"∀(x: ?a) X(x) -> X = univ" ) {
    simp.w( "extAxiom" )
  }

  val emptycomp = lemma( hof" comp(empty) = univ", "simp" ) {
    simp.w( "extAxiom" )
  }

  val emptysubset = lemma( hof"empty ⊂ X", "simp" ) {
    simp.w( "subset" )
  }

  val subsetuniv = lemma( hof" X ⊂ univ", "simp" ) {
    simp.w( "subset" )
  }

  val unionunion = lemma( hof"X ∪ X = X", "simp" ) {
    simp.w( "extAxiom" )
    allR
    prop
  }

  val unionassoc = lemma( hof" X ∪ (Y ∪ Z) = (X ∪ Y) ∪ Z" ) {
    simp.w( "extAxiom" )
    allR
    prop
  }

  val unioncomm = lemma( hof"X ∪ Y = Y ∪ X" ) {
    simp.w( "extAxiom" )
    allR
    prop
  }

  val subsetunion = lemma( hof" X ∪ Y = Y <-> X ⊂ Y" ) {
    simp.w( "subset", "extAxiom" )
    escrgt
  }

  val subsetintersect = lemma( hof" X ∩ Y = X <-> X ⊂ Y" ) {
    simp.w( "subset", "extAxiom" )
    escrgt
  }

  val intersectintersect = lemma( hof"X ∩ X = X", "simp" ) {
    simp.w( "extAxiom" )
    allR
    prop
  }

  val intersectassoc = lemma( hof" X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z" ) {
    simp.w( "extAxiom" )
    allR
    prop
  }

  val intersectcomm = lemma( hof" X ∩ Y = Y ∩ X" ) {
    simp.w( "extAxiom" )
    allR
    prop
  }

  val univunion1 = lemma( hof" X ∪ univ = univ", "simp" ) {
    simp.w( "subsetunion" )
  }

  val univunion2 = lemma( hof" univ ∪ X = univ", "simp" ) {
    include( "unioncomm" )
    rewrite ltr "unioncomm" in "g"
    simp
  }

  val univintersect1 = lemma( hof" X ∩ univ = X", "simp" ) {
    simp.w( "subsetintersect" )
  }

  val univinterset2 = lemma( hof" univ ∩ X = X", "simp" ) {
    include( "intersectcomm" )
    rewrite ltr "intersectcomm" in "g"
    simp
  }

  val emptyunion1 = lemma( hof" X ∪ empty = X", "simp" ) {
    include( "unioncomm" )
    rewrite ltr "unioncomm" in "g"
    simp.w( "subsetunion" )
  }

  val emptyunion2 = lemma( hof" empty ∪ X = X", "simp" ) {
    simp.w( "subsetunion" )
  }

  val emptyintersect1 = lemma( hof" X ∩ empty = empty", "simp" ) {
    include( "intersectcomm" )
    rewrite ltr "intersectcomm" in "g"
    simp.w( "subsetintersect" )
  }

  val emptyintersect2 = lemma( hof" empty ∩ X = empty", "simp" ) {
    simp.w( "subsetintersect" )
  }
  val demorgan1 = lemma( hof"comp(X ∪ Y) = comp(X) ∩ comp(Y)" ) { simp.w( "extAxiom" ) }
  val demorgan2 = lemma( hof" comp(X ∩ Y) = comp(X) ∪ comp(Y)" ) { simp.w( "extAxiom" ) }

  val unionintersectdistrib = lemma( hof" (X ∪ Y) ∩ Z = (X ∩ Z) ∪ (Y ∩ Z)" ) {
    simp.w( "extAxiom" )
    escrgt
  }

  val intersectuniondistrib = lemma( hof" (X ∩ Y) ∪ Z = (X ∪ Z) ∩ (Y ∪ Z)" ) {
    simp.w( "extAxiom" )
    escrgt
  }

  val insertuniv = lemma( hof" insert univ x = univ", "simp" ) {
    simp.w( "extAxiom" )
  }

  val insertunion = lemma( hof" bigunion (insert P x) = (bigunion P) ∪ x" ) {
    simp.w( "extAxiom" )
    escrgt
  }

  val insertintersect = lemma( hof" bigintersect (insert P x) = (bigintersect P) ∩ x" ) {
    simp.w( "extAxiom" )
    escrgt
  }

  val pairsetunion = lemma( hof" bigunion (pairset X Y) = X ∪ Y", "simp" ) {
    simp.w( "extAxiom" )
    escrgt
  }

  val pairsetintersect = lemma( hof" bigintersect (pairset X Y) = X ∩ Y", "simp" ) {
    simp.w( "extAxiom" )
    escrgt
  }

  val bigunionempty = lemma( hof" bigunion empty = empty", "simp" ) {
    simp.w( "extAxiom" )
  }

  val bigintersectempty = lemma( hof" bigintersect empty = univ", "simp" ) {
    simp.w( "extAxiom" )
  }

  val pairsetelem1 = lemma( hof" (pairset x y) x", "simp" ) {
    simp
  }

  val pairsetelem2 = lemma( hof" (pairset x y) y", "simp" ) {
    simp
  }

}