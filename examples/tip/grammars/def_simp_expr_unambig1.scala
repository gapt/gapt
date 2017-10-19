
package at.logic.gapt.examples.tip.grammars

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_simp_expr_unambig1 extends TipProblemDefinition {

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
      TBase( "Tok" ),
      List(
        TipConstructor( hoc"'C' :Tok", List() ),
        TipConstructor( hoc"'D' :Tok", List() ),
        TipConstructor( hoc"'X' :Tok", List() ),
        TipConstructor( hoc"'Y' :Tok", List() ),
        TipConstructor( hoc"'Pl' :Tok", List() ) ) ),
    TipDatatype(
      TBase( "list" ),
      List(
        TipConstructor( hoc"'nil' :list", List() ),
        TipConstructor( hoc"'cons' :Tok>list>list", List( hoc"'head' :list>Tok", hoc"'tail' :list>list" ) ) ) ),
    TipDatatype(
      TBase( "E" ),
      List(
        TipConstructor( hoc"'Plus' :E>E>E", List( hoc"'Plus_0' :E>E", hoc"'Plus_1' :E>E" ) ),
        TipConstructor( hoc"'EX' :E", List() ),
        TipConstructor( hoc"'EY' :E", List() ) ) ) )

  override def uninterpretedConsts = List(
    hoc"'nil' :list",
    hoc"'D' :Tok",
    hoc"'Y' :Tok",
    hoc"'EX' :E",
    hoc"'cons' :Tok>list>list",
    hoc"'C' :Tok",
    hoc"'Pl' :Tok",
    hoc"'Plus' :E>E>E",
    hoc"'X' :Tok",
    hoc"'tail' :list>list",
    hoc"'Plus_1' :E>E",
    hoc"'EY' :E",
    hoc"'head' :list>Tok",
    hoc"'Plus_0' :E>E" )

  override def assumptions = List()

  override def functions = List(
    TipFun(
      hoc"'append' :list>list>list",
      List(
        hof"(append(nil:list, y:list): list) = y",
        hof"(append(cons(z:Tok, xs:list): list, y:list): list) = cons(z, append(xs, y))" ) ),
    TipFun(
      hoc"'lin' :E>list",
      List(
        hof"(lin(Plus(#v(a: E), #v(b: E)): E): list) =   append(append(append(append(cons(C:Tok, nil:list): list, lin(#v(a: E))): list,         cons(Pl, nil)), lin(#v(b: E))), cons(D, nil))",
        hof"(lin(EX:E): list) = cons(#c(X: Tok), nil:list)",
        hof"(lin(EY:E): list) = cons(#c(Y: Tok), nil:list)" ) ) )

  override def goal = hof"∀u ∀v ((lin(u:E): list) = lin(v) ⊃ u = v)"
}

