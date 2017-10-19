
package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_32 extends TipProblemDefinition {

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
      hoc"'min2' :Nat>Nat>Nat",
      List(
        hof"(min2(#c(Z: Nat), y:Nat): Nat) = #c(Z: Nat)",
        hof"(min2(S(z:Nat): Nat, #c(Z: Nat)): Nat) = #c(Z: Nat)",
        hof"(min2(S(z:Nat): Nat, S(y2)): Nat) = S(min2(z, y2))" ) ) )

  override def goal = hof"∀a ∀b (min2(a:Nat, b:Nat): Nat) = min2(b, a)"
}

