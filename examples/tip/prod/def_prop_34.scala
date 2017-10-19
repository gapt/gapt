
package at.logic.gapt.examples.tip.prod

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_34 extends TipProblemDefinition {

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
      hoc"'mult2' :Nat>Nat>Nat>Nat",
      List(
        hof"(mult2(#c(Z: Nat), y:Nat, z:Nat): Nat) = z",
        hof"(mult2(S(x2:Nat): Nat, y:Nat, z:Nat): Nat) = mult2(x2, y, plus(y, z))" ) ),
    TipFun(
      hoc"'mult' :Nat>Nat>Nat",
      List(
        hof"(mult(#c(Z: Nat), y:Nat): Nat) = #c(Z: Nat)",
        hof"(mult(S(z:Nat): Nat, y:Nat): Nat) = plus(y, mult(z, y))" ) ) )

  override def goal = hof"∀x ∀y (mult(x:Nat, y:Nat): Nat) = mult2(x, y, #c(Z: Nat))"
}

