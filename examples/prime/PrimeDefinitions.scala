package at.logic.gapt.examples.prime

import at.logic.gapt.expr.ExpressionParseHelper.Splice
import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.expr._
import at.logic.gapt.formats.babel.{ Notation, Precedence }
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
  ctx += Notation.Infix( "+", Precedence.plusMinus )
  ctx += hoc"'*': nat>nat>nat"
  ctx += Notation.Infix( "*", Precedence.timesDiv )
  ctx += hoc"'<': nat>nat>o"
  ctx += Notation.Infix( "<", Precedence.infixRel )

  // Theory axioms
  ctx += "distrib1" -> hcl":- (x + 1) * y + x + 1 = (x + 1) * (y + 1)"
  ctx += "mul_ac1" -> hcl"x = y + z * (u * v) :- x = y + z * u * v"
  ctx += "mul_ac2" -> hcl"x = y + z * (u * v) :- x = y + z * v * u"
  ctx += "divrem" -> hcl"k < m, k + l*m = 0 + r*m :- 0 = k"
  ctx += "mul_smon" -> hcl"1 < x, x*y = x*z + 1 :-"
  ctx += "add_two" -> hcl"1 + (x + 1) = 1 :-"
  ctx += "add_mul1" -> hcl":- k + (n * (l + (1 + 1)) + l * (k + 1) + 1) = n + (n + (k + 1)) * (l + 1)"
  ctx += "one_neq_mul" -> hcl"1 < x, 1 = y * x :-"
  ctx += "zero_add" -> hcl":- 0+x = x"
  ctx += "mul_one" -> hcl":- x*1 = x"
  ctx += "mul_add_one" -> hcl"x*y+1=1 :- x+1=1, y+1=1"
  ctx += "add_one_neq_one" -> hcl"1<x, x+1 = 1 :-"
  ctx += "mul_assoc" -> hcl":- x*(y*z)=(x*y)*z"
  ctx += "mul_comm" -> hcl":- x*y = y*x"
  ctx += "zero_lt" -> hcl"x < y :- 0 < y"
  ctx += "neq_one" -> hcl"1<y, x=0+z*y, x=1 :-"
  ctx += "add_comm_zero" -> hcl"y*z=x :- x=0+z*y"
  ctx += "distrib2" -> hcl":- x + y1*z + y2*z = x + (y1+y2)*z"

  //Definitions
  ctx += hof" set_1{?a}(k : ?a) = ( λl l = k )"
  ctx += hof" ν(k,l) = ( λm ∃n m = k + n * l )"
  ctx += hof" U k l = ( λm ∃i ((i < l ∧ ¬i = k ) ∧ ν(i,l,m)) )"
  ctx += hof" DIV l k = ( ∃m l * m = k )"
  ctx += hof" PRIME k = ( 1 < k ∧ ∀l(DIV(l,k) -> (l = 1 ∨ l = k)) )"
  ctx += hof" subset{?a} (X : ?a > o) Y = ( ∀n (X(n) -> Y(n)) )"
  ctx += hof" empty{?a} (X : ?a > o) = ( ¬ ∃n X(n) )"
  ctx += hof" compN{?a} (X : ?a > o) = ( λx ¬X(x) )"
  ctx += hof" union{?a} (X : ?a > o) Y = ( λx (X(x) ∨ Y(x)) )"
  ctx += hof" intersection{?a} (X : ?a > o) Y = ( λx (X(x) ∧ Y(x)) )"
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
