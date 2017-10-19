
package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_14 extends TipProblemDefinition {

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
      hoc"'filter' :fun1>list>list",
      List(
        hof"(filter(x:fun1, nil:list): list) = nil",
        hof"¬apply1(x:fun1, z:sk) ⊃   (filter(x, cons(z, xs:list): list): list) = filter(x, xs)",
        hof"apply1(x:fun1, z:sk) ⊃   (filter(x, cons(z, xs:list): list): list) = cons(z, filter(x, xs))" ) ),
    TipFun(
      hoc"'append' :list>list>list",
      List(
        hof"(append(nil:list, y:list): list) = y",
        hof"(append(cons(z:sk, xs:list): list, y:list): list) = cons(z, append(xs, y))" ) ) )

  override def goal = hof"∀p   ∀xs   ∀ys   (filter(p:fun1, append(xs:list, ys:list): list): list) =     append(filter(p, xs), filter(p, ys))"
}

