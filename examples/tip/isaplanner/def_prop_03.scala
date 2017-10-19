
package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_03 extends TipProblemDefinition {

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
      hoc"'le' :Nat>Nat>o",
      List(
        hof"le(#c(Z: Nat), y:Nat): o",
        hof"¬le(S(z:Nat): Nat, #c(Z: Nat))",
        hof"(le(S(z:Nat): Nat, S(x2)) ⊃ le(z, x2)) ∧ (le(z, x2) ⊃ le(S(z), S(x2)))" ) ),
    TipFun(
      hoc"'equal' :Nat>Nat>o",
      List(
        hof"equal(#c(Z: Nat), #c(Z: Nat)): o",
        hof"¬equal(#c(Z: Nat), S(z:Nat): Nat)",
        hof"¬equal(S(x2:Nat): Nat, #c(Z: Nat))",
        hof"(equal(S(x2:Nat): Nat, S(y2)) ⊃ equal(x2, y2)) ∧   (equal(x2, y2) ⊃ equal(S(x2), S(y2)))" ) ),
    TipFun(
      hoc"'count' :Nat>list>Nat",
      List(
        hof"(count(x:Nat, nil:list): Nat) = #c(Z: Nat)",
        hof"¬equal(x:Nat, z:Nat) ⊃ (count(x, cons(z, ys:list): list): Nat) = count(x, ys)",
        hof"equal(x:Nat, z:Nat) ⊃ (count(x, cons(z, ys:list): list): Nat) = S(count(x, ys))" ) ),
    TipFun(
      hoc"'append' :list>list>list",
      List(
        hof"(append(nil:list, y:list): list) = y",
        hof"(append(cons(z:Nat, xs:list): list, y:list): list) = cons(z, append(xs, y))" ) ) )

  override def goal = hof"∀n ∀xs ∀ys le(count(n:Nat, xs:list): Nat, count(n, append(xs, ys:list)))"
}

