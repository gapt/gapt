
package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_06 extends TipProblemDefinition {

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
      hoc"'minus' :Nat>Nat>Nat",
      List(
        hof"(minus(#c(Z: Nat), y:Nat): Nat) = #c(Z: Nat)",
        hof"(minus(S(z:Nat): Nat, #c(Z: Nat)): Nat) = S(z)",
        hof"(minus(S(z:Nat): Nat, S(x2)): Nat) = minus(z, x2)" ) ) )

  override def goal = hof"∀n ∀m (minus(n:Nat, plus(n, m:Nat): Nat): Nat) = #c(Z: Nat)"
}

