
package at.logic.gapt.examples.tip.prod

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_33 extends TipProblemDefinition {

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
      TBase( "Nat" ),
      List(
        TipConstructor( hoc"'Z' :Nat", List() ),
        TipConstructor( hoc"'S' :Nat>Nat", List( hoc"'p' :Nat>Nat" ) ) ) ) )

  override def uninterpretedConsts = List(
    hoc"'S' :Nat>Nat",
    hoc"'p' :Nat>Nat",
    hoc"'Z' :Nat" )

  override def assumptions = List()

  override def functions = List(
    TipFun(
      hoc"'plus' :Nat>Nat>Nat",
      List(
        hof"(plus(#c(Z: Nat), y:Nat): Nat) = y",
        hof"(plus(S(z:Nat): Nat, y:Nat): Nat) = S(plus(z, y))" ) ),
    TipFun(
      hoc"'one' :Nat",
      List( hof"(one:Nat) = S(#c(Z: Nat))" ) ),
    TipFun(
      hoc"'mult' :Nat>Nat>Nat",
      List(
        hof"(mult(#c(Z: Nat), y:Nat): Nat) = #c(Z: Nat)",
        hof"(mult(S(z:Nat): Nat, y:Nat): Nat) = plus(y, mult(z, y))" ) ),
    TipFun(
      hoc"'qfac' :Nat>Nat>Nat",
      List(
        hof"(qfac(#c(Z: Nat), y:Nat): Nat) = y",
        hof"(qfac(S(z:Nat): Nat, y:Nat): Nat) = qfac(z, mult(S(z), y))" ) ),
    TipFun(
      hoc"'fac' :Nat>Nat",
      List(
        hof"(fac(#c(Z: Nat)): Nat) = S(#c(Z: Nat))",
        hof"(fac(S(y:Nat): Nat): Nat) = mult(S(y), fac(y))" ) ) )

  override def goal = hof"∀x (fac(x:Nat): Nat) = qfac(x, one:Nat)"
}

