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

  def splitgt0( label: String ): Tactical[Unit] =
    for {
      goal <- currentGoal
      subst <- syntacticMatching( hof"a*b + 1 = 1", goal( label ) ).
        toTactical( s"$label is no product", goal )
      l = NewLabel( goal.labelledSequent, label )
      _ <- cut( l, subst( hof"a+1=1 ∨ b+1=1" ) )
      _ <- destruct( l ); _ <- theory
      _ <- forget( label ); _ <- renameLabel( l ) to label
      _ <- orL( label )
    } yield ()

  def prodgt0( i: Int ): LKProof = Lemma(
    ( "gt0" -> hof"${prod( i )} + 1 = 1" ) +:
      ( "fk" -> hof"${F( k )}" ) +:
      Sequent()
  ) {
      unfold( prod( i ).name ) in "gt0"

      if ( i > 0 ) splitgt0( "gt0" ) andThen insert( prodgt0( i - 1 ) ) else skip

      unfold( F( k ).name ) in "fk"
      allL( "fk", p( i ) ).forget; decompose; destruct( "fk_1" )
      Tactical.sequence( for ( j <- i to k reverse ) yield repeat( unfold( P( j ).name, "union", "set_1" ) in "fk_1" ) )
      decompose; trivial
      unfold( "PRIME" ) in "fk_1"; decompose

      theory
    }

  val proof =
    Lemma(
      ( "fk" -> hof"${F( k )}" ) +:
        ( "primediv" -> hof"'PRIME-DIV'" ) +: Sequent()
    ) {
        unfold( "PRIME-DIV" ) in "primediv"
        allL( "primediv", le"${prod( k )} + 1" ).forget
        destruct( "primediv" ) onAll decompose

        insert( prodgt0( k ) )

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
