package at.logic.gapt.examples.induction

import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Context, Sequent }

object numbers extends TacticsProof {
  ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )

  ctx += hoc"'+': nat>nat>nat"
  val plusth = ( "plus0" -> hof"∀x 0+x=x" ) +:
    ( "plussuc" -> hof"∀x∀y s(x)+y=s(x+y)" ) +:
    Sequent()

  val plus0r = Lemma( plusth :+ ( "goal" -> hof"∀x x+0=x" ) ) {
    decompose; induction( hov"x:nat" )
    rewrite.many ltr "plus0"; refl
    rewrite.many ltr ( "plussuc", "IHx_0" ); refl
  }

  val plussucr = Lemma( plusth :+ ( "goal" -> hof"∀x∀y x+s(y)=s(x+y)" ) ) {
    decompose; induction( hov"x:nat" )
    rewrite.many ltr "plus0"; refl
    rewrite.many ltr ( "plussuc", "IHx_0" ); refl
  }

  val pluscomm = Lemma( plusth :+ ( "goal" -> hof"∀x∀y x+y=y+x" ) ) {
    include( "plus0r", plus0r )
    include( "plussucr", plussucr )
    decompose; induction( hov"x:nat" )
    rewrite.many ltr ( "plus0", "plus0r" ); refl
    rewrite.many ltr ( "plussucr", "plussuc", "IHx_0" ); refl
  }
}
