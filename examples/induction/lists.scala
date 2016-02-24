package at.logic.gapt.examples.induction

import at.logic.gapt.examples.TacticsProof
import at.logic.gapt.proofs.{ Context, FiniteContext, Sequent }
import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.extractRecSchem

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

  val appth =
    ( "consapp" -> hof"!x!y!z cons(x,y)+z = cons(x,y+z)" ) +:
      ( "nilapp" -> hof"!x nil+x = x" ) +:
      Sequent()

  val revth =
    ( "revcons" -> hof"!x!y rev(cons(x,y)) = rev(y)+cons(x,nil)" ) +:
      ( "revnil" -> hof"rev(nil) = nil" ) +:
      Sequent()

  val appnil = Lemma( appth :+ ( "goal" -> hof"!x x+nil = x" ) ) {
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

  val appassoc = Lemma( appth :+ ( "goal" -> hof"!x!y!z x+(y+z) = (x+y)+z" ) ) {
    induction onAll decompose
    rewrite.many ltr "nilapp"; refl
    rewrite.many ltr ( "consapp", "IHx_0" ); refl
  }

  val apprev = Lemma( ( appth ++ revth ) :+ ( "goal" -> hof"!x!y rev(x+y) = rev(y) + rev(x)" ) ) {
    include( "appnil", appnil )
    include( "appassoc", appassoc )
    induction onAll decompose
    rewrite.many ltr ( "nilapp", "revnil", "appnil" ); refl
    rewrite.many ltr ( "consapp", "revcons", "IHx_0", "appassoc" ); refl
  }

  val revrev = Lemma( ( appth ++ revth ) :+ ( "goal" -> hof"!x rev(rev(x)) = x" ) ) {
    include( "apprev", apprev )
    induction onAll decompose
    rewrite.many ltr "revnil"; refl
    rewrite.many ltr ( "revcons", "apprev", "IHx_0", "revnil", "nilapp", "consapp" ); refl
  }

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
