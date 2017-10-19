
package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_43 extends TipProblemDefinition {

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
    hoc"'tail' :list>list",
    hoc"'head' :list>sk" )

  override def assumptions = List()

  override def functions = List(
    TipFun(
      hoc"'takeWhile' :fun1>list>list",
      List(
        hof"(takeWhile(x:fun1, nil:list): list) = nil",
        hof"¬apply1(x:fun1, z:sk) ⊃ (takeWhile(x, cons(z, xs:list): list): list) = nil",
        hof"apply1(x:fun1, z:sk) ⊃   (takeWhile(x, cons(z, xs:list): list): list) = cons(z, takeWhile(x, xs))" ) ),
    TipFun(
      hoc"'dropWhile' :fun1>list>list",
      List(
        hof"(dropWhile(x:fun1, nil:list): list) = nil",
        hof"¬apply1(x:fun1, z:sk) ⊃   (dropWhile(x, cons(z, xs:list): list): list) = cons(z, xs)",
        hof"apply1(x:fun1, z:sk) ⊃   (dropWhile(x, cons(z, xs:list): list): list) = dropWhile(x, xs)" ) ),
    TipFun(
      hoc"'append' :list>list>list",
      List(
        hof"(append(nil:list, y:list): list) = y",
        hof"(append(cons(z:sk, xs:list): list, y:list): list) = cons(z, append(xs, y))" ) ) )

  override def goal = hof"∀p   ∀xs   (append(takeWhile(p:fun1, xs:list): list, dropWhile(p, xs): list): list) = xs"
}

