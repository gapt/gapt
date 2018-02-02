package at.logic.gapt.examples.prime

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk.LKProof

case class euclid( k: Int ) extends PrimeDefinitions {
  def ldivprod( i: Int ): LKProof = {
    val sequent = hols"linp: P $i l  :-  div: DIV l (prod $i)"
    if ( i == 0 )
      Proof( sequent ) {
        unfold( "P", "set_1" ) in "linp"
        unfold( "DIV", "prod" ) in "div"
        exR( le"1" ).forget
        rewrite ltr "linp" in "div"
        theory
      }
    else
      Proof( sequent ) {
        unfold( "P" ).atMost( 1 ) in "linp"
        unfold( "union" ) in "linp"
        unfold( "DIV" ) in "div"
        unfold( "prod" ).atMost( 1 ) in "div"
        destruct( "linp" )
        by {
          include( "IH", ldivprod( i - 1 ) )
          unfold( "DIV" ) in "IH"
          decompose
          exR( le"m * p $i" ).forget
          rewrite rtl "IH"
          theory
        }
        by {
          unfold( "set_1" ) in "linp"
          exR( le"prod ${i - 1}" ).forget
          rewrite ltr "linp" in "div"
          theory
        }
      }
  }

  def splitgt0( label: String ): Tactic[Unit] = Tactic {
    for {
      goal <- currentGoal
      subst <- syntacticMatching( hof"a*b + 1 = 1", goal( label ) ).
        toTactic( s"$label is no product" )
      l = NewLabel( goal.labelledSequent, label )
      _ <- cut( l, subst( hof"a+1=1 ∨ b+1=1" ) )
      _ <- destruct( l ); _ <- theory
      _ <- forget( label ); _ <- renameLabel( l ) to label
      _ <- orL( label )
    } yield ()
  }

  def prodgt0( i: Int ): LKProof = Proof( hols"gt0: prod $i + 1 = 1, fk: F $k :-" ) {
    unfold( "prod" ) atMost 1 in "gt0"

    if ( i > 0 ) splitgt0( "gt0" ) andThen insert( prodgt0( i - 1 ) ) else skip

    unfold( "F" ) in "fk"
    allL( "fk", le"p $i" ).forget; decompose; destruct( "fk_1" )
    Tactic.sequence( for ( j <- i to k reverse ) yield unfold( "P", "union", "set_1" ) in "fk_1" )
    decompose; trivial
    unfold( "PRIME" ) in "fk_1"; decompose

    theory
  }

  val proof =
    Lemma( hols"fk: F $k, primediv: 'PRIME-DIV' :-" ) {
      unfold( "PRIME-DIV" ) in "primediv"
      allL( "primediv", le"prod $k + 1" ).forget
      destruct( "primediv" ) onAll decompose

      insert( prodgt0( k ) )

      unfold( "F" ) in "fk"
      allL( "fk", le"l: nat" ).forget; decompose
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
