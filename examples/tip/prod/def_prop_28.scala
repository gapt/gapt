
package at.logic.gapt.examples.tip.prod

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_28 extends TipProblemDefinition {

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
      TBase( "list2" ),
      List(
        TipConstructor( hoc"'nil2' :list2", List() ),
        TipConstructor( hoc"'cons2' :sk>list2>list2", List( hoc"'head2' :list2>sk", hoc"'tail2' :list2>list2" ) ) ) ),
    TipDatatype(
      TBase( "list" ),
      List(
        TipConstructor( hoc"'nil' :list", List() ),
        TipConstructor( hoc"'cons' :list2>list>list", List( hoc"'head' :list>list2", hoc"'tail' :list>list" ) ) ) ) )

  override def uninterpretedConsts = List(
    hoc"'nil' :list",
    hoc"'nil2' :list2",
    hoc"'cons' :list2>list>list",
    hoc"'tail2' :list2>list2",
    hoc"'tail' :list>list",
    hoc"'cons2' :sk>list2>list2",
    hoc"'head' :list>list2",
    hoc"'head2' :list2>sk" )

  override def assumptions = List()

  override def functions = List(
    TipFun(
      hoc"'append' :list2>list2>list2",
      List(
        hof"(append(nil2:list2, y:list2): list2) = y",
        hof"(append(cons2(z:sk, xs:list2): list2, y:list2): list2) = cons2(z, append(xs, y))" ) ),
    TipFun(
      hoc"'rev' :list2>list2",
      List(
        hof"(rev(nil2:list2): list2) = nil2",
        hof"(rev(cons2(y:sk, xs:list2): list2): list2) = append(rev(xs), cons2(y, nil2))" ) ),
    TipFun(
      hoc"'qrevflat' :list>list2>list2",
      List(
        hof"(qrevflat(nil:list, y:list2): list2) = y",
        hof"(qrevflat(cons(xs:list2, xss:list): list, y:list2): list2) =   qrevflat(xss, append(rev(xs): list2, y))" ) ),
    TipFun(
      hoc"'revflat' :list>list2",
      List(
        hof"(revflat(nil:list): list2) = nil2",
        hof"(revflat(cons(xs:list2, xss:list): list): list2) =   append(revflat(xss), rev(xs): list2)" ) ) )

  override def goal = hof"∀x (revflat(x:list): list2) = qrevflat(x, nil2:list2)"
}

