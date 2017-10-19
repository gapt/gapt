
package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_19 extends TipProblemDefinition {

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
      TBase( "list" ),
      List(
        TipConstructor( hoc"'nil' :list", List() ),
        TipConstructor( hoc"'cons' :sk>list>list", List( hoc"'head' :list>sk", hoc"'tail' :list>list" ) ) ) ),
    TipDatatype(
      TBase( "Nat" ),
      List(
        TipConstructor( hoc"'Z' :Nat", List() ),
        TipConstructor( hoc"'S' :Nat>Nat", List( hoc"'p' :Nat>Nat" ) ) ) ) )

  override def uninterpretedConsts = List(
    hoc"'S' :Nat>Nat",
    hoc"'nil' :list",
    hoc"'cons' :sk>list>list",
    hoc"'p' :Nat>Nat",
    hoc"'tail' :list>list",
    hoc"'Z' :Nat",
    hoc"'head' :list>sk" )

  override def assumptions = List()

  override def functions = List(
    TipFun(
      hoc"'minus' :Nat>Nat>Nat",
      List(
        hof"(minus(#c(Z: Nat), y:Nat): Nat) = #c(Z: Nat)",
        hof"(minus(S(z:Nat): Nat, #c(Z: Nat)): Nat) = S(z)",
        hof"(minus(S(z:Nat): Nat, S(x2)): Nat) = minus(z, x2)" ) ),
    TipFun(
      hoc"'len' :list>Nat",
      List(
        hof"(len(nil:list): Nat) = #c(Z: Nat)",
        hof"(len(cons(y:sk, xs:list): list): Nat) = S(len(xs))" ) ),
    TipFun(
      hoc"'drop' :Nat>list>list",
      List(
        hof"(drop(#c(Z: Nat), y:list): list) = y",
        hof"(drop(S(z:Nat): Nat, nil:list): list) = nil",
        hof"(drop(S(z:Nat): Nat, cons(x2:sk, x3:list): list): list) = drop(z, x3)" ) ) )

  override def goal = hof"∀n ∀xs (len(drop(n:Nat, xs:list): list): Nat) = minus(len(xs), n)"
}

