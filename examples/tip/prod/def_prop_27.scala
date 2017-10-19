
package at.logic.gapt.examples.tip.prod

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_27 extends TipProblemDefinition {

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
      hoc"'qrev' :list>list>list",
      List(
        hof"(qrev(nil:list, y:list): list) = y",
        hof"(qrev(cons(z:sk, xs:list): list, y:list): list) = qrev(xs, cons(z, y))" ) ),
    TipFun(
      hoc"'append' :list>list>list",
      List(
        hof"(append(nil:list, y:list): list) = y",
        hof"(append(cons(z:sk, xs:list): list, y:list): list) = cons(z, append(xs, y))" ) ),
    TipFun(
      hoc"'rev' :list>list",
      List(
        hof"(rev(nil:list): list) = nil",
        hof"(rev(cons(y:sk, xs:list): list): list) = append(rev(xs), cons(y, nil))" ) ) )

  override def goal = hof"∀x (rev(x:list): list) = qrev(x, nil:list)"
}

