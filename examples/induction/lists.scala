package at.logic.gapt.examples.induction

import at.logic.gapt.examples.TacticsProof
import at.logic.gapt.proofs.{ Context, FiniteContext, Sequent }
import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic._

object lists extends TacticsProof {

  implicit val context = FiniteContext(
    constants = Set(
      hoc"nil: list", hoc"cons: i>list>list",
      hoc"'+': list>list>list",
      hoc"rev: list>list"
    ),
    typeDefs = Set(
      Context.iTypeDef, Context.oTypeDef,
      Context.InductiveType(
        TBase( "list" ),
        Seq( hoc"nil: list", hoc"cons: i>list>list" )
      )
    )
  )

  val th =
    ( "consapp" -> hof"!x!y!z cons(x,y)+z = cons(x,y+z)" ) +:
      ( "nilapp" -> hof"!x nil+x = x" ) +:
      ( "revcons" -> hof"!x!y rev(cons(x,y)) = rev(y)+cons(x,nil)" ) +:
      ( "revnil" -> hof"rev(nil) = nil" ) +:
      Sequent()

  val appnil = Lemma( th :+ ( "goal" -> hof"!x x+nil = x" ) ) {
    induction
    chain( "nilapp" )
    rewrite.many ltr ( "consapp", "IHx_0" ) in "goal"
    refl
  }

  Lemma( th :+ ( "example" -> hof"!x x + nil + nil = x" ) ) {
    include( "appnil", appnil )
    decompose
    rewrite.many ltr "appnil"
    refl
  }

}
