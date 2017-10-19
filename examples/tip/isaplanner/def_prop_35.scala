
package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_35 extends TipProblemDefinition {

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
        TipConstructor( hoc"'cons' :sk>list>list", List( hoc"'head' :list>sk", hoc"'tail' :list>list" ) ) ) ) )

  override def uninterpretedConsts = List(
    hoc"'nil' :list",
    hoc"'apply1' :fun1>sk>o",
    hoc"'cons' :sk>list>list",
    hoc"'lam' :fun1",
    hoc"'tail' :list>list",
    hoc"'head' :list>sk" )

  override def assumptions = List(
    hof"∀x ((apply1(lam:fun1, x:sk) ⊃ ⊥) ∧ (⊥ ⊃ apply1(lam, x)))" )

  override def functions = List(
    TipFun(
      hoc"'dropWhile' :fun1>list>list",
      List(
        hof"(dropWhile(x:fun1, nil:list): list) = nil",
        hof"¬apply1(x:fun1, z:sk) ⊃   (dropWhile(x, cons(z, xs:list): list): list) = cons(z, xs)",
        hof"apply1(x:fun1, z:sk) ⊃   (dropWhile(x, cons(z, xs:list): list): list) = dropWhile(x, xs)" ) ) )

  override def goal = hof"∀xs (dropWhile(lam:fun1, xs:list): list) = xs"
}

