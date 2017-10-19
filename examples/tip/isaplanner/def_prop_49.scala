
package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_49 extends TipProblemDefinition {

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
        TipConstructor( hoc"'cons' :sk>list>list", List( hoc"'head' :list>sk", hoc"'tail' :list>list" ) ) ) ) )

  override def uninterpretedConsts = List(
    hoc"'nil' :list",
    hoc"'cons' :sk>list>list",
    hoc"'tail' :list>list",
    hoc"'head' :list>sk" )

  override def assumptions = List()

  override def functions = List(
    TipFun(
      hoc"'butlast' :list>list",
      List(
        hof"(butlast(nil:list): list) = nil",
        hof"(butlast(cons(y:sk, nil:list): list): list) = nil",
        hof"(butlast(cons(y:sk, cons(x2:sk, x3:list): list)): list) =   cons(y, butlast(cons(x2, x3)))" ) ),
    TipFun(
      hoc"'append' :list>list>list",
      List(
        hof"(append(nil:list, y:list): list) = y",
        hof"(append(cons(z:sk, xs:list): list, y:list): list) = cons(z, append(xs, y))" ) ),
    TipFun(
      hoc"'butlastConcat' :list>list>list",
      List(
        hof"(butlastConcat(x:list, nil:list): list) = butlast(x)",
        hof"(butlastConcat(x:list, cons(z:sk, x2:list): list): list) =   append(x, butlast(cons(z, x2)): list)" ) ) )

  override def goal = hof"∀xs ∀ys (butlast(append(xs:list, ys:list): list): list) = butlastConcat(xs, ys)"
}

