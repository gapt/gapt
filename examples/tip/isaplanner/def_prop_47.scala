
package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.formats.tip.TipProblemDefinition

object def_prop_47 extends TipProblemDefinition {

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
      TBase( "Tree" ),
      List(
        TipConstructor( hoc"'Leaf' :Tree", List() ),
        TipConstructor( hoc"'Node' :Tree>sk>Tree>Tree", List( hoc"'Node_0' :Tree>Tree", hoc"'Node_1' :Tree>sk", hoc"'Node_2' :Tree>Tree" ) ) ) ),
    TipDatatype(
      TBase( "Nat" ),
      List(
        TipConstructor( hoc"'Z' :Nat", List() ),
        TipConstructor( hoc"'S' :Nat>Nat", List( hoc"'p' :Nat>Nat" ) ) ) ) )

  override def uninterpretedConsts = List(
    hoc"'S' :Nat>Nat",
    hoc"'Node_2' :Tree>Tree",
    hoc"'Node' :Tree>sk>Tree>Tree",
    hoc"'Node_1' :Tree>sk",
    hoc"'Leaf' :Tree",
    hoc"'p' :Nat>Nat",
    hoc"'Node_0' :Tree>Tree",
    hoc"'Z' :Nat" )

  override def assumptions = List()

  override def functions = List(
    TipFun(
      hoc"'mirror' :Tree>Tree",
      List(
        hof"(mirror(Leaf:Tree): Tree) = Leaf",
        hof"(mirror(Node(#v(l: Tree), y:sk, #v(r: Tree)): Tree): Tree) =   Node(mirror(#v(r: Tree)), y, mirror(#v(l: Tree)))" ) ),
    TipFun(
      hoc"'max2' :Nat>Nat>Nat",
      List(
        hof"(max2(#c(Z: Nat), y:Nat): Nat) = y",
        hof"(max2(S(z:Nat): Nat, #c(Z: Nat)): Nat) = S(z)",
        hof"(max2(S(z:Nat): Nat, S(x2)): Nat) = S(max2(z, x2))" ) ),
    TipFun(
      hoc"'height' :Tree>Nat",
      List(
        hof"(height(Leaf:Tree): Nat) = #c(Z: Nat)",
        hof"(height(Node(#v(l: Tree), y:sk, #v(r: Tree)): Tree): Nat) =   S(max2(height(#v(l: Tree)), height(#v(r: Tree))): Nat)" ) ) )

  override def goal = hof"∀b (height(mirror(b:Tree): Tree): Nat) = height(b)"
}

