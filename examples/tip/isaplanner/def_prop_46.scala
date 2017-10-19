
package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_46 extends TipProblemDefinition {

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
      TBase( "Pair" ),
      List(
        TipConstructor( hoc"'Pair2' :sk>sk>Pair", List( hoc"'first' :Pair>sk", hoc"'second' :Pair>sk" ) ) ) ),
    TipDatatype(
      TBase( "list" ),
      List(
        TipConstructor( hoc"'nil' :list", List() ),
        TipConstructor( hoc"'cons' :Pair>list>list", List( hoc"'head' :list>Pair", hoc"'tail' :list>list" ) ) ) ) )

  override def uninterpretedConsts = List(
    hoc"'nil' :list",
    hoc"'second' :Pair>sk",
    hoc"'nil2' :list2",
    hoc"'cons' :Pair>list>list",
    hoc"'tail2' :list2>list2",
    hoc"'tail' :list>list",
    hoc"'Pair2' :sk>sk>Pair",
    hoc"'cons2' :sk>list2>list2",
    hoc"'head' :list>Pair",
    hoc"'first' :Pair>sk",
    hoc"'head2' :list2>sk" )

  override def assumptions = List()

  override def functions = List(
    TipFun(
      hoc"'zip' :list2>list2>list",
      List(
        hof"(#c(zip: list2>list2>list)(nil2:list2, y:list2): list) = nil",
        hof"(#c(zip: list2>list2>list)(cons2(z:sk, x2:list2): list2, nil2:list2): list) =   nil",
        hof"(#c(zip: list2>list2>list)(cons2(z:sk, x2:list2): list2, cons2(x3, x4)): list) =   cons(Pair2(z, x3): Pair, #c(zip: list2>list2>list)(x2, x4): list)" ) ) )

  override def goal = hof"∀xs (#c(zip: list2>list2>list)(nil2:list2, xs:list2): list) = nil"
}

