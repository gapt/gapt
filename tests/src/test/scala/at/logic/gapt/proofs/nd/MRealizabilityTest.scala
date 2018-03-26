package at.logic.gapt.proofs.nd

import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.Context.{ InductiveType, PrimRecFun }
import org.specs2.mutable.Specification

class MRealizabilityTest extends Specification {

  "addRecorsors" in {
    "naturalNumbers" in {
      var ctx = Context()

      ctx += InductiveType(
        ty"nat",
        hoc"0 : nat",
        hoc"s : nat > nat" )

      implicit var systemT = MRealizability.systemT( ctx )

      val plusTwo = le"natRec(s(s(0)))(^z1 ^z2 (s(z2)))"

      normalize( plusTwo( le"s(s(s(0)))" ) ) must_== le"s(s(s(s(s(0)))))"
    }
    "pairs+naturalNumbers" in {
      var ctx = Context()

      ctx += InductiveType(
        ty"nat",
        hoc"0 : nat",
        hoc"s : nat > nat" )
      ctx += PrimRecFun(
        hoc"'+': nat>nat>nat",
        "0 + x = x",
        "s(x) + y = s(x + y)" )( ctx )
      ctx += InductiveType(
        ty"conjj ?c  ?b",
        hoc"pairr{?c ?b}: ?c > ?b > conjj ?c ?b" )

      implicit var systemT = MRealizability.systemT( ctx )

      val sumPair = le"conjjRec (^(x:nat) ^(y:nat) (x + y) )"

      normalize( sumPair( le"pairr(s(0),s(s(0)))" ) ) must_== le"s(s(s(0)))"
    }
    "binaryTrees" in {
      var ctx = Context()

      ctx += InductiveType(
        ty"bitree ?a",
        hoc"leaf{?a}: ?a > bitree ?a",
        hoc"node{?a}: bitree ?a > bitree ?a > bitree ?a" )

      implicit var systemT = MRealizability.systemT( ctx )

      systemT += Definition(
        Const( "mirror", ty"bitree ?a > bitree ?a", List( ty"?a" ) ),
        le"bitreeRec( (^(x:?a)leaf(x)), (^(z1:bitree ?a)^(z2:bitree ?a)^(z3:bitree ?a)^(z4:bitree ?a) node(z4,z2)) )" )

      normalize( le"mirror( node(leaf(x), node(leaf(y), node(leaf(z1), leaf(z2)))) )" ) must_==
        le"node(node(node(leaf(z2), leaf(z1)), leaf(y)), leaf(x))"
    }
    "lists" in {
      var ctx = Context()

      ctx += InductiveType(
        ty"nat",
        hoc"0 : nat",
        hoc"s : nat > nat" )
      ctx += PrimRecFun(
        hoc"'+': nat>nat>nat",
        "0 + x = x",
        "s(x) + y = s(x + y)" )( ctx )
      ctx += InductiveType(
        ty"list ?a",
        hoc"nil{?a}: list ?a",
        hoc"cons{?a}: ?a > list ?a > list ?a" )

      implicit var systemT = MRealizability.systemT( ctx )

      systemT += Definition(
        Const( "length", ty"list ?a > nat", List( ty"?a" ) ),
        le"listRec(0,^(z1:?a)^(z2: list ?a)^(z3:nat) s(z3))" )

      normalize( le"length( cons(1, cons(2, cons(3,nil))) )" ) must_== le"s(s(s(0)))"

      val sumList = le"listRec(0,(^v ^l ^r v+r))"

      normalize( sumList( le"cons(0, cons(s(0), cons(s(s(0)), nil)))" ) ) must_== le"s(s(s(0)))"
    }

  }

  "empty" in {
    "emptyType" in {
      implicit var ctx = Context()

      ctx += InductiveType(
        ty"nat",
        hoc"0 : nat",
        hoc"s : nat > nat" )
      ctx += InductiveType(
        ty"1",
        hoc"i : 1" )

      val nat = ty"nat"
      val one = ty"1"

      MRealizability.remEmpProgType( one ) must_== one

      val natToNat: Ty = nat ->: nat
      val oneToNat: Ty = one ->: nat

      MRealizability.remEmpProgType( natToNat ) must_== natToNat
      MRealizability.remEmpProgType( oneToNat ) must_== nat
      MRealizability.remEmpProgType( natToNat ->: one ) must_== one

      val a = TBase( "conj", oneToNat, one )

      MRealizability.remEmpProgType( a ) must_== nat
    }
  }
}