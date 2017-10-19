
package at.logic.gapt.examples.tip.prod

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_35 extends TipProblemDefinition {

  import at.logic.gapt.expr._
  import at.logic.gapt.formats.tip.{ TipDatatype, TipFun, TipConstructor }

  override def sorts = List(
    TBase( "sk" ) )

  override def datatypes = List(
    TipDatatype(
      TBase( "o" ),
      List(
        TipConstructor( hoc"'⊤' :o", List() ),
        TipConstructor( hoc"'⊥' :o", List() ) ) ),
    TipDatatype(
      TBase( "Nat" ),
      List(
        TipConstructor( hoc"'Z' :Nat", List() ),
        TipConstructor( hoc"'S' :Nat>Nat", List( hoc"'p' :Nat>Nat" ) ) ) ) )

  override def uninterpretedConsts = List(
    hoc"'S' :Nat>Nat",
    hoc"'p' :Nat>Nat",
    hoc"'Z' :Nat" )

  override def assumptions = List()

  override def functions = List(
    TipFun(
      hoc"'plus' :Nat>Nat>Nat",
      List(
        hof"(plus(#c(Z: Nat), y:Nat): Nat) = y",
        hof"(plus(S(z:Nat): Nat, y:Nat): Nat) = S(plus(z, y))" ) ),
    TipFun(
      hoc"'one' :Nat",
      List( hof"(one:Nat) = S(#c(Z: Nat))" ) ),
    TipFun(
      hoc"'mult' :Nat>Nat>Nat",
      List(
        hof"(mult(#c(Z: Nat), y:Nat): Nat) = #c(Z: Nat)",
        hof"(mult(S(z:Nat): Nat, y:Nat): Nat) = plus(y, mult(z, y))" ) ),
    TipFun(
      hoc"'qexp' :Nat>Nat>Nat>Nat",
      List(
        hof"(qexp(x:Nat, #c(Z: Nat), z:Nat): Nat) = z",
        hof"(qexp(x:Nat, S(#v(n: Nat)): Nat, z:Nat): Nat) = qexp(x, #v(n: Nat), mult(x, z))" ) ),
    TipFun(
      hoc"'exp' :Nat>Nat>Nat",
      List(
        hof"(exp(x:Nat, #c(Z: Nat)): Nat) = S(#c(Z: Nat))",
        hof"(exp(x:Nat, S(#v(n: Nat)): Nat): Nat) = mult(x, exp(x, #v(n: Nat)))" ) ) )

  override def goal = hof"∀x ∀y (exp(x:Nat, y:Nat): Nat) = qexp(x, y, one:Nat)"
}

