package at.logic.gapt.examples.prime

import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.gaptic.TacticsProof

/**
 * Contains definitions for Euclid's and Furstenberg's prime proofs.
 */
trait PrimeDefinitions extends TacticsProof {
  def k: Int

  // Types
  ctx += Context.Sort( "i" )

  // Constants
  ctx += Const( "0", Ti )
  ctx += Const( "1", Ti )
  ctx += Const( "+", Ti -> ( Ti -> Ti ) )
  ctx += Const( "*", Ti -> ( Ti -> Ti ) )
  ctx += Const( "<", Ti -> ( Ti -> To ) )

  Seq(
    hof" ∀x ∀y (x + 1) * y + x + 1 = (x + 1) * (y + 1)",
    hof" ∀x ∀y ∀z ∀u ∀v (x = y + z * (u * v ) -> x = y + z * u  * v)",
    hof" ∀x ∀y ∀z ∀u ∀v (x = y + z * (u * v ) -> x = y + z * v  * u)",
    hof" ∀x ∀y (x = y -> y = x)",
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
  ctx += hof" set_1(k) = ( λl l = k )"
  ctx += hof" ν(k,l) = ( λm ∃n m = k + n * l )"
  ctx += hof" U k l = ( λm ∃i ((i < l ∧ ¬i = k ) ∧ ν(i,l,m)) )"
  ctx += hof" DIV l k = ( ∃m l * m = k )"
  ctx += hof" PRIME k = ( 1 < k ∧ ∀l(DIV(l,k) -> (l = 1 ∨ l = k)) )"
  ctx += hof" subset X Y = ( ∀n (X(n) -> Y(n)) )"
  ctx += hof" empty X = ( ¬∃n X(n) )"
  ctx += hof" compN X = ( λx ¬X(x) )"
  ctx += hof" union X Y = ( λx (X(x) ∨ Y(x)) )"
  ctx += hof" intersection X Y = ( λx (X(x) ∧ Y(x)) )"
  ctx += hof" O X = ( ∀m (X(m) -> ∃l subset(ν(m, l+1), X)) )"
  ctx += hof" C X = ( O(compN(X)) )"
  ctx += hof" INF X = ( ∀k ∃l X(k+(l + 1)) )"
  ctx += "PRE" -> fof" ∀k (0 < k -> ∃m k = m+1)"
  ctx += "REM" -> hof" ∀l (0 < l -> ∀m∃k (k < l ∧ ν(k,l)(m) ))"
  ctx += "PRIME-DIV" -> hof" ∀m ((¬ m = 1) -> ∃l(PRIME l ∧ DIV l m) )"

  // Definitions that depend on k
  val p = ( 0 to k ) map ( i => FOLConst( s"p_$i" ) )
  val F = ( 0 to k ) map ( i => Const( s"F[$i]", To ) )
  val S = ( 0 to k ) map ( i => Const( s"S[$i]", Ti -> To ) )
  val P = ( 0 to k ) map ( i => Const( s"P[$i]", Ti -> To ) )
  val Q = ( 0 to k ) map ( i => Const( s"Q[$i]", To ) )
  val R = ( 0 to k ) map ( i => Const( s"R[$i]", To ) )
  val prod = ( 0 to k ) map ( i => Const( s"prod[$i]", Ti ) )

  for ( c <- p ) ctx += c

  ctx += hof" 'P[0]' = set_1(p_0)"
  ctx += hof" 'S[0]' = ν(0, p_0)"
  ctx += hof" 'Q[0]' = PRIME(${p( 0 )})"
  ctx += hof" 'R[0]' = (∀y (${P( 0 )}(y) -> PRIME y))"
  ctx += hof"${prod( 0 )} = ${p( 0 )}"

  for ( i <- 1 to k ) {
    ctx += hof" ${P( i )} = union(${P( i - 1 )}, set_1 ${p( i )})"
    ctx += hof" ${S( i )} = union(${S( i - 1 )}, ν(0, ${p( i )}))"
    ctx += hof" ${Q( i )} = (${Q( i - 1 )} ∧ PRIME(${p( i )}))"
    ctx += hof" ${R( i )} = (∀y (${P( i )} y -> PRIME y))"
    ctx += hof" ${prod( i )} = (${prod( i - 1 )} * ${p( i )})"
  }

  ctx += hof" ${F( k )} =  (∀l (PRIME(l) <-> ${P( k )}(l)))"
}
