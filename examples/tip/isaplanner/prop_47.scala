package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.Context.InductiveType
import gapt.proofs.Sequent
import gapt.proofs.gaptic._
import gapt.proofs.gaptic.tactics.AnalyticInductionTactic._

object prop_47 extends TacticsProof {

  // Sorts
  ctx += TBase( "sk" )
  // Inductive types
  ctx += InductiveType( ty"Tree", hoc"'Leaf' :Tree", hoc"'Node' :Tree>sk>Tree>Tree" )
  ctx += InductiveType( ty"Nat", hoc"'Z' :Nat", hoc"'S' :Nat>Nat" )
  //Constants

  //Function constants
  ctx += hoc"'mirror' :Tree>Tree"
  ctx += hoc"'max2' :Nat>Nat>Nat"
  ctx += hoc"'height' :Tree>Nat"

  val sequent =
    hols"""
        def_Node_0: ∀x0 ∀x1 ∀x2 (Node_0(Node(x0:Tree, x1:sk, x2:Tree): Tree): Tree) = x0,
        def_Node_1: ∀x0 ∀x1 ∀x2 (Node_1(Node(x0:Tree, x1:sk, x2:Tree): Tree): sk) = x1,
        def_Node_2: ∀x0 ∀x1 ∀x2 (Node_2(Node(x0:Tree, x1:sk, x2:Tree): Tree): Tree) = x2,
        def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
        def_mirror_0: (mirror(Leaf:Tree): Tree) = Leaf,
        def_mirror_1: ∀l   ∀y   ∀r   (mirror(Node(l:Tree, y:sk, r:Tree): Tree): Tree) =     Node(mirror(r), y, mirror(l)),
        def_max2_0: ∀y (max2(#c(Z: Nat), y:Nat): Nat) = y,
        def_max2_1: ∀z (max2(S(z:Nat): Nat, #c(Z: Nat)): Nat) = S(z),
        def_max2_2: ∀z ∀x2 (max2(S(z:Nat): Nat, S(x2)): Nat) = S(max2(z, x2)),
        def_height_0: (height(Leaf:Tree): Nat) = #c(Z: Nat),
        def_height_1: ∀l   ∀y   ∀r   (height(Node(l:Tree, y:sk, r:Tree): Tree): Nat) =     S(max2(height(l), height(r)): Nat),
        constr_inj_0: ∀y0 ∀y1 ∀y2 ¬(Leaf:Tree) = Node(y0:Tree, y1:sk, y2:Tree),
        constr_inj_1: ∀y0 ¬#c(Z: Nat) = S(y0:Nat)
        :-
        goal: ∀b (height(mirror(b:Tree): Tree): Nat) = height(b)
  """

  val mirror_definition = List(
    "mi1" -> hof"mirror(Leaf) = Leaf",
    "mi2" -> hof"∀l ∀y ∀r mirror(Node(l, y, r)) = Node(mirror(r), y, mirror(l))" )

  val max_definition = List(
    "ma1" -> hof"∀y max2(Z, y) = y",
    "ma2" -> hof"∀z max2(S(z), Z) = S(z)",
    "ma3" -> hof"∀z ∀x2 max2(S(z), S(x2)) = S(max2(z, x2))" )

  val max_comm_goal = hof"!x !y max2(x,y) = max2(y,x)"
  val max_comm = max_definition ++: Sequent() :+ "goal" -> max_comm_goal
  val max_comm_proof = Lemma( max_comm ) {
    analyticInduction withAxioms sequentialAxioms.forAllVariables.forLabel( "goal" )
  }

  val proof = Lemma( sequent ) {
    cut( "max_comm", max_comm_goal ); insert( max_comm_proof )
    allR; analyticInduction
  }

}
