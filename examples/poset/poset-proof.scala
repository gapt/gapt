package at.logic.gapt.examples.poset

import at.logic.gapt.examples.TacticsProof
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Context, FiniteContext, Sequent }
import at.logic.gapt.proofs.gaptic._

object proof extends TacticsProof {
  implicit var ctx = FiniteContext()
  ctx += Context.Sort( "i" )
  ctx += hoc"f: i>i>i"
  ctx += hoc"'=':i>i>o"
  ctx += hoc"a:i"
  ctx += hoc"b:i"
  ctx += hoc"c:i"
  ctx += hoc"d:i"

  val axioms =
    ( "eqrefl" -> hof"!x x=x" ) +:
      ( "eqsymm" -> hof"!x!y (x=y -> y=x)" ) +:
      ( "eqtrans" -> hof"!x!y!z (x=y & y=z -> x=z)" ) +:
      ( "eqfcongr" -> hof"!x!y!u!v (x=y & u=v -> f(x,u) = f(y,v))" ) +:
      ( "fcomm" -> hof"!x!y f(x,y) = f(y,x)" ) +:
      ( "fassoc" -> hof"!x!y!z f(f(x,y),z) = f(x,f(y,z))" ) +:
      Sequent()

  val trans = Lemma( axioms :+ ( "trans" -> hof"!x!y!z (f(x,y)=x & f(y,z)=y -> f(x,z)=x)" ) ) {
    decompose
    chain( "eqtrans" ).subst( hov"y" -> le"f(f(x,y), z)" )
    chain( "eqsymm" ); chain( "eqfcongr" ); prop; chain( "eqrefl" )
    chain( "eqtrans" ).subst( hov"y" -> le"f(x, f(y,z))" )
    chain( "fassoc" )
    chain( "eqtrans" ).subst( hov"y" -> le"f(x, y)" )
    chain( "eqfcongr" ); chain( "eqrefl" ); prop
    prop
  }

  val asymm = Lemma( axioms :+ ( "asymm" -> hof"!u!v (f(u,v)=u & f(v,u)=v -> u=v)" ) ) {
    decompose
    chain( "eqtrans" ).subst( hov"y" -> le"f(u, v)" )
    chain( "eqsymm" ); prop
    chain( "eqtrans" ).subst( hov"y" -> le"f(v, u)" )
    chain( "fcomm" )
    prop
  }

  val cycleImpliesEqual3 =
    Lemma( axioms :+ ( "goal" -> hof"f(a,b)=a & f(b,c)=b & f(c,a)=c -> a=b & b=c" ) ) {
      include( "trans", trans )
      include( "asymm", asymm )

      // right side of the cut
      decompose; destruct( "goal_1" ) onAll ( chain( "asymm" ) andThen prop )

      // f(b,a)=b
      chain( "trans" ).subst( hov"y" -> le"c" ); repeat( prop )

      // f(c,b)=c
      chain( "trans" ).subst( hov"y" -> le"a" ); repeat( prop )
    }

  val cycleImpliesEqual4 =
    Lemma( axioms :+ ( "goal" -> hof"f(a,b)=a & f(b,c)=b & f(c,d)=c & f(d,a)=d -> a=b & b=c & c=d" ) ) {
      include( "trans", trans )
      include( "asymm", asymm )
      decompose

      // first show f(c,a)=c
      cut( hof"f(c, a) = c", "leq_c_a" ); forget( "goal_1" )
      chain( "trans" ).subst( hov"y" -> le"d" ); prop; prop

      // and f(a,c)=a
      cut( hof"f(a, c) = a", "leq_a_c" ); forget( "goal_1" )
      chain( "trans" ).subst( hov"y" -> le"b" ); prop; prop

      // now show the final goals
      repeat( destruct( "goal_1" ) )
      ( chain( "asymm" ) andThen prop ).onAllSubGoals

      // f(b,a)=b
      chain( "trans" ).subst( hov"y" -> le"c" ); repeat( prop )

      // f(c,b)=c
      chain( "trans" ).subst( hov"y" -> le"a" ); repeat( prop )

      // f(d,c)=c
      chain( "trans" ).subst( hov"y" -> le"a" ); repeat( prop )
    }

}