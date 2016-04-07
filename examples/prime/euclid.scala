package at.logic.gapt.examples.prime
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.LKProof

case class euclid( k: Int ) extends PrimeDefinitions {
  def ldivprod( i: Int ): LKProof = {
    val sequent =
      ( "linp" -> hof"${P( i )} l" ) +:
        Sequent() :+
        ( "div" -> hof"DIV l ${prod( i )}" )

    if ( i == 0 )
      Lemma( sequent ) {
        repeat( unfold( P( i ).name, "set_1" ) in "linp" )
        repeat( unfold( "DIV", prod( i ).name ) in "div" )
        exR( le"1" ).forget
        rewrite ltr "linp" in "div"
        theory
      }
    else
      Lemma( sequent ) {
        repeat( unfold( P( i ).name, "union" ) in "linp" )
        repeat( unfold( "DIV", prod( i ).name ) in "div" )
        destruct( "linp" )

        include( "IH", ldivprod( i - 1 ) )
        unfold( "DIV" ) in "IH"
        decompose
        exR( le"m * ${p( i )}" ).forget
        rewrite rtl "IH"
        theory

        unfold( "set_1" ) in "linp"
        exR( prod( i - 1 ) ).forget
        rewrite ltr "linp" in "div"
        theory
      }
  }

  def splitgt0( label: String ) =
    for {
      goal <- currentGoal
      subst <- syntacticMatching( hof"a*b + 1 = 1", goal( label ) ).
        toTactical( s"$label is no product", goal )
      l = NewLabel( goal.labelledSequent, label )
      _ <- cut( l, subst( hof"a+1=1 ∧ b+1=1" ) )
      _ <- destruct( l ); _ <- theory; _ <- theory
      _ <- forget( label )
      ls <- andL( l )
    } yield ls

  val prodgt0 =
    Lemma(
      ( "gt0" -> hof"${prod( k )} + 1 = 1" ) +:
        ( "fk" -> hof"${F( k )}" ) +:
        Sequent()
    ) {
        unfold( F( k ).name ) in "fk"
        allL( "fk", p( k ) ).forget; decompose; destruct( "fk_1" )
        repeat( unfold( P( k ).name, "union", "set_1" ) in "fk_1" ); decompose; trivial
        unfold( "PRIME" ) in "fk_1"; decompose

        unfold( prod( k ).name ) in "gt0"
        splitgt0( "gt0" ) orElse skip

        theory
      }

  val proof =
    Lemma(
      ( "fk" -> hof"${F( k )}" ) +:
        ( "pre" -> hof"PRE" ) +:
        ( "primediv" -> hof"'PRIME-DIV'" ) +: Sequent()
    ) {
        unfold( "PRIME-DIV" ) in "primediv"
        allL( "primediv", le"${prod( k )} + 1" ).forget
        destruct( "primediv" ) onAll decompose

        insert( prodgt0 )

        unfold( s"F[$k]" ) in "fk"
        allL( "fk", le"l" ).forget; decompose
        destruct( "fk_0" ); trivial
        include( "ldivprod", ldivprod( k ) )
        unfold( "PRIME" ) in "primediv_0"
        unfold( "DIV" ) in ( "ldivprod", "primediv_1" )
        decompose
        rewrite rtl "ldivprod" in "primediv_1"
        theory
      }
}
object euclid3 extends euclid( 3 )
