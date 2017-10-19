
package at.logic.gapt.examples.tip.prod

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_16 extends TipProblemDefinition {

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
      hoc"'even' :Nat>o",
      List(
        hof"even(#c(Z: Nat)): o",
        hof"¬even(S(#c(Z: Nat)): Nat)",
        hof"(even(S(S(z:Nat): Nat)) ⊃ even(z)) ∧ (even(z) ⊃ even(S(S(z))))" ) ) )

  override def goal = hof"∀x even(plus(x:Nat, x): Nat)"
}

