
package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_16 extends TipProblemDefinition {

  import at.logic.gapt.expr._
  import at.logic.gapt.formats.tip.{ TipDatatype, TipFun, TipConstructor }

  override def sorts = List()

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
        TipConstructor( hoc"'S' :Nat>Nat", List( hoc"'p' :Nat>Nat" ) ) ) ),
    TipDatatype(
      TBase( "list" ),
      List(
        TipConstructor( hoc"'nil' :list", List() ),
        TipConstructor( hoc"'cons' :Nat>list>list", List( hoc"'head' :list>Nat", hoc"'tail' :list>list" ) ) ) ) )

  override def uninterpretedConsts = List(
    hoc"'nil' :list",
    hoc"'S' :Nat>Nat",
    hoc"'cons' :Nat>list>list",
    hoc"'p' :Nat>Nat",
    hoc"'tail' :list>list",
    hoc"'Z' :Nat",
    hoc"'head' :list>Nat" )

  override def assumptions = List()

  override def functions = List(
    TipFun(
      hoc"'last' :list>Nat",
      List(
        hof"(last(nil:list): Nat) = #c(Z: Nat)",
        hof"(last(cons(y:Nat, nil:list): list): Nat) = y",
        hof"(last(cons(y:Nat, cons(x2:Nat, x3:list): list)): Nat) = last(cons(x2, x3))" ) ) )

  override def goal = hof"∀x ∀xs ((xs:list) = nil ⊃ (last(cons(x:Nat, xs): list): Nat) = x)"
}

