
package at.logic.gapt.examples.tip.prod

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
      hoc"'length' :list>Nat",
      List(
        hof"(length(nil:list): Nat) = #c(Z: Nat)",
        hof"(length(cons(y:sk, xs:list): list): Nat) = S(length(xs))" ) ),
    TipFun(
      hoc"'append' :list>list>list",
      List(
        hof"(append(nil:list, y:list): list) = y",
        hof"(append(cons(z:sk, xs:list): list, y:list): list) = cons(z, append(xs, y))" ) ),
    TipFun(
      hoc"'rotate' :Nat>list>list",
      List(
        hof"(rotate(#c(Z: Nat), y:list): list) = y",
        hof"(rotate(S(z:Nat): Nat, nil:list): list) = nil",
        hof"(rotate(S(z:Nat): Nat, cons(x2:sk, x3:list): list): list) =   rotate(z, append(x3, cons(x2, nil)))" ) ) )

  override def goal = hof"∀x (rotate(length(x:list): Nat, x): list) = x"
}

