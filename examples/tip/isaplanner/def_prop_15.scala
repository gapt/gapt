
package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_15 extends TipProblemDefinition {

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
      hoc"'lt' :Nat>Nat>o",
      List(
        hof"¬lt(x:Nat, #c(Z: Nat))",
        hof"lt(#c(Z: Nat), S(z:Nat): Nat): o",
        hof"(lt(S(x2:Nat): Nat, S(z)) ⊃ lt(x2, z)) ∧ (lt(x2, z) ⊃ lt(S(x2), S(z)))" ) ),
    TipFun(
      hoc"'len' :list>Nat",
      List(
        hof"(len(nil:list): Nat) = #c(Z: Nat)",
        hof"(len(cons(y:Nat, xs:list): list): Nat) = S(len(xs))" ) ),
    TipFun(
      hoc"'ins' :Nat>list>list",
      List(
        hof"(ins(x:Nat, nil:list): list) = cons(x, nil)",
        hof"¬lt(x:Nat, z:Nat) ⊃ (ins(x, cons(z, xs:list): list): list) = cons(z, ins(x, xs))",
        hof"lt(x:Nat, z:Nat) ⊃ (ins(x, cons(z, xs:list): list): list) = cons(x, cons(z, xs))" ) ) )

  override def goal = hof"∀x ∀xs (len(ins(x:Nat, xs:list): list): Nat) = S(len(xs))"
}

