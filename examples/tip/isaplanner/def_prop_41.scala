
package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_41 extends TipProblemDefinition {

  import at.logic.gapt.expr._
  import at.logic.gapt.formats.tip.{ TipDatatype, TipFun, TipConstructor }

  override def sorts = List(
    TBase( "sk" ),
    TBase( "fun1" ) )

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
    hoc"'apply1' :fun1>sk>sk",
    hoc"'cons' :sk>list>list",
    hoc"'p' :Nat>Nat",
    hoc"'tail' :list>list",
    hoc"'Z' :Nat",
    hoc"'head' :list>sk" )

  override def assumptions = List()

  override def functions = List(
    TipFun(
      hoc"'take' :Nat>list>list",
      List(
        hof"(take(#c(Z: Nat), y:list): list) = nil",
        hof"(take(S(z:Nat): Nat, nil:list): list) = nil",
        hof"(take(S(z:Nat): Nat, cons(x2:sk, x3:list): list): list) = cons(x2, take(z, x3))" ) ),
    TipFun(
      hoc"'map2' :fun1>list>list",
      List(
        hof"(map2(x:fun1, nil:list): list) = nil",
        hof"(map2(x:fun1, cons(z:sk, xs:list): list): list) =   cons(apply1(x, z), map2(x, xs))" ) ) )

  override def goal = hof"∀n   ∀f   ∀xs   (take(n:Nat, map2(f:fun1, xs:list): list): list) = map2(f, take(n, xs))"
}

