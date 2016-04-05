package at.logic.gapt.examples.induction

import at.logic.gapt.proofs.{ Context, FiniteContext, Sequent }
import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.extractRecSchem

object lists extends TacticsProof {
  ctx += Context.Sort( "i" )
  ctx += Context.InductiveType( "list", hoc"nil: list", hoc"cons: i>list>list" )

  ctx += hoc"'+': list>list>list"
  val appth =
    ( "consapp" -> hof"∀x ∀y ∀z cons(x,y)+z = cons(x,y+z)" ) +:
      ( "nilapp" -> hof"∀x nil+x = x" ) +:
      Sequent()

  val appnil = Lemma( appth :+ ( "goal" -> hof"∀x x+nil = x" ) ) {
    induction
    chain( "nilapp" )
    rewrite.many ltr ( "consapp", "IHx_0" ) in "goal"
    refl
  }

  Lemma( appth :+ ( "example" -> hof"x + nil + nil = x" ) ) {
    include( "appnil", appnil )
    rewrite.many ltr "appnil"
    refl
  }

  val appassoc = Lemma( appth :+ ( "goal" -> hof"∀x ∀y ∀z x+(y+z) = (x+y)+z" ) ) {
    induction onAll decompose
    rewrite.many ltr "nilapp"; refl
    rewrite.many ltr ( "consapp", "IHx_0" ); refl
  }

  ctx += hoc"rev: list>list"
  val revth =
    ( "revcons" -> hof"∀x∀y rev(cons(x,y)) = rev(y)+cons(x,nil)" ) +:
      ( "revnil" -> hof"rev(nil) = nil" ) +:
      Sequent()

  val apprev = Lemma( ( appth ++ revth ) :+ ( "goal" -> hof"∀x ∀y rev(x+y) = rev(y) + rev(x)" ) ) {
    include( "appnil", appnil )
    include( "appassoc", appassoc )
    induction onAll decompose
    rewrite.many ltr ( "nilapp", "revnil", "appnil" ); refl
    rewrite.many ltr ( "consapp", "revcons", "IHx_0", "appassoc" ); refl
  }

  val revrev = Lemma( ( appth ++ revth ) :+ ( "goal" -> hof"∀x rev(rev(x)) = x" ) ) {
    include( "apprev", apprev )
    induction onAll decompose
    rewrite.many ltr "revnil"; refl
    rewrite.many ltr ( "revcons", "apprev", "IHx_0", "revnil", "nilapp", "consapp" ); refl
  }

  ctx += hoc"map: (i>i) > (list>list)"
  val mapth =
    ( "mapcons" -> hof"∀f ∀x ∀xs map f (cons x xs) = cons (f x) (map f xs)" ) +:
      ( "mapnil" -> hof"∀f map f nil = nil" ) +:
      Sequent()

  val mapapp = Lemma( ( appth ++ mapth ) :+ ( "goal" -> hof"∀f ∀xs ∀ys map f (xs + ys) = map f xs + map f ys" ) ) {
    allR; induction onAll decompose
    rewrite.many ltr ( "nilapp", "mapnil" ); refl
    rewrite.many ltr ( "consapp", "mapcons", "IHxs_0" ); refl
  }

  val maprev = Lemma( ( appth ++ revth ++ mapth ) :+ ( "goal" -> hof"∀f ∀xs map f (rev xs) = rev (map f xs)" ) ) {
    include( "mapapp", mapapp )
    allR; induction
    rewrite.many ltr ( "revnil", "mapnil" ); refl
    rewrite.many ltr ( "revcons", "mapcons", "mapapp", "IHxs_0", "mapnil" ); refl
  }

  ctx += hof"(f*g) x = f (g x)"
  Lemma( Sequent() :+ ( "example" -> hof"(f*g) x = f (g x)" ) ) { unfold( "*" ) in "example"; refl }

  val mapfusion = Lemma( mapth :+ ( "goal" -> hof"∀f ∀g ∀xs map (f*g) xs = map f (map g xs)" ) ) {
    allR; allR; induction
    rewrite.many ltr "mapnil"; refl
    rewrite.many ltr ( "mapcons", "IHxs_0" ); unfold( "*" ) in "goal"; refl
  }

  // Note: we cannot prove constructor injectivity using the induction rule.

  if ( false ) {
    val rs = extractRecSchem( Lemma( ( appth ++ revth ) :+ ( "goal" -> hof"rev(rev(x)) = x" ) ) {
      include( "revrev", revrev )
      chain( "revrev" )
    } )

    println( rs )
    rs.parametricLanguage( le"cons(x, cons(y, cons(z, nil)))" ) map { _.toSigRelativeString } foreach println
    // not valid because inductive lemma is instantiated with rev(...)
  }

}
