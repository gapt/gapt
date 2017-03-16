package at.logic.gapt.examples.prime

import at.logic.gapt.expr.ExpressionParseHelper.Splice
import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.Context.PrimRecFun
import at.logic.gapt.proofs.gaptic.TacticsProof

/**
 * Contains definitions for Euclid's and Furstenberg's prime proofs.
 */
trait PrimeDefinitions extends TacticsProof {
  def k: Int

  // Types
  ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += hof"1 = s 0"
  implicit def spliceNum( i: Int ): Splice[Expr] =
    if ( i == 0 ) le"0" else le"s ${spliceNum( i - 1 )}"

  // Constants
  ctx += hoc"'+': nat>nat>nat"
  ctx += hoc"'*': nat>nat>nat"
  ctx += hoc"'<': nat>nat>o"

  Seq(
    hof" ∀x ∀y (x + 1) * y + x + 1 = (x + 1) * (y + 1)",
    hof" ∀x ∀y ∀z ∀u ∀v (x = y + z * (u * v ) -> x = y + z * u  * v)",
    hof" ∀x ∀y ∀z ∀u ∀v (x = y + z * (u * v ) -> x = y + z * v  * u)",
    hof" ∀(x:nat) ∀y (x = y -> y = x)",
    hof" ∀k ∀l ∀r ∀m (k < m -> k + l*m = 0 + r*m -> 0 = k)",
    hof" ∀x ∀y ∀z (1 < x ⊃ x*y != x*z + 1)",
    hof" ∀x ¬1 + (x + 1) = 1",
    hof" ∀k ∀n ∀l k + (n * (l + (1 + 1)) + l * (k + 1) + 1) = n + (n + (k + 1)) * (l + 1)",
    hof" ∀x ∀y (1 < x -> ¬ 1 = y * x)",
    hof" ∀x 0+x = x",
    hof" ∀x x*1 = x",
    hof" ∀x∀y (x*y+1=1 ⊃ x+1=1 ∨ y+1=1)",
    hof" ∀x (1<x ⊃ x+1 != 1)",
    hof" ∀x∀y∀z x*(y*z)=(x*y)*z",
    hof" ∀x∀y x*y=y*x",
    hof" ∀x ∀y (x < y -> 0 < y)",
    hof" ∀x ∀y ∀z (1<y ∧ x=0+z*y ⊃ x!=1)",
    hof" ∀x ∀y ∀z (y*z=x ⊃ x=0+z*y)",
    hof" ∀x ∀y1 ∀y2 ∀z x + y1*z + y2*z = x + (y1+y2)*z"
  ).flatMap( CNFp( _ ) ).foreach( ctx += _ )

  //Definitions
  ctx += hof" set_1(k : ?a) = ( λl l = k )"
  ctx += hof" ν(k,l) = ( λm ∃n m = k + n * l )"
  ctx += hof" U k l = ( λm ∃i ((i < l ∧ ¬i = k ) ∧ ν(i,l,m)) )"
  ctx += hof" DIV l k = ( ∃m l * m = k )"
  ctx += hof" PRIME k = ( 1 < k ∧ ∀l(DIV(l,k) -> (l = 1 ∨ l = k)) )"
  ctx += hof" subset (X : ?a > o) Y = ( ∀n (X(n) -> Y(n)) )"
  ctx += hof" empty (X : ?a > o) = ( ¬∃n X(n) )"
  ctx += hof" compN (X : ?a > o) = ( λx ¬X(x) )"
  ctx += hof" union (X : ?a > o) Y = ( λx (X(x) ∨ Y(x)) )"
  ctx += hof" intersection (X : ?a > o) Y = ( λx (X(x) ∧ Y(x)) )"
  ctx += hof" O X = ( ∀m (X(m) -> ∃l subset(ν(m, l+1), X)) )"
  ctx += hof" C X = ( O(compN(X)) )"
  ctx += hof" INF X = ( ∀k ∃l X(k+(l + 1)) )"
  ctx += "PRE" -> hof" ∀k (0 < k -> ∃m k = m+1)"
  ctx += "REM" -> hof" ∀l (0 < l -> ∀m∃k (k < l ∧ ν(k,l)(m) ))"
  ctx += "PRIME-DIV" -> hof" ∀m ((¬ m = 1) -> ∃l(PRIME l ∧ DIV l m) )"

  // Definitions that depend on k
  ctx += hoc"p : nat > nat"

  ctx += PrimRecFun( hoc"P : nat > nat > o", "P 0 = set_1 (p 0)", "P (s i) = union (P i) (set_1 (p (s i)))" )
  ctx += PrimRecFun( hoc"S : nat > nat > o", "S 0 = ν(0, p 0)", "S (s i) = union (S i) (ν(0, p (s i)))" )
  ctx += PrimRecFun( hoc"Q: nat > o", "Q 0 = PRIME (p 0)", "Q (s i) = (Q i ∧ PRIME (p (s i)))" )
  ctx += hof"R i = (∀y (P i y -> PRIME y))"
  ctx += PrimRecFun( hoc"prod : nat > nat", "prod 0 = p 0", "prod (s i) = prod i * p (s i)" )

  ctx += hof"F k =  (∀l (PRIME(l) <-> P k l))"
}
