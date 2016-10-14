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
    hof"∀x ∀y (x = y -> y = x)",
    hof" ∀k ∀l ∀r ∀m (k < m -> k + l*m = 0 + r*m -> 0 = k)",
    hof"∀x ∀y ∀z (1 < x ⊃ x*y != x*z + 1)",
    hof" ∀x ¬1 + (x + 1) = 1",
    hof" ∀k ∀n ∀l k + (n * (l + (1 + 1)) + l * (k + 1) + 1) = n + (n + (k + 1)) * (l + 1)",
    hof" ∀x ∀y (1 < x -> ¬ 1 = y * x)",
    hof" ∀x 0+x = x",
    hof" ∀x x*1 = x",
    hof"∀x∀y (x*y+1=1 ⊃ x+1=1 ∨ y+1=1)",
    hof"∀x (1<x ⊃ x+1 != 1)",
    hof" ∀x∀y∀z x*(y*z)=(x*y)*z",
    hof" ∀x∀y x*y=y*x",
    hof" ∀x ∀y (x < y -> 0 < y)",
    hof"∀x ∀y ∀z (1<y ∧ x=0+z*y ⊃ x!=1)",
    hof"∀x ∀y ∀z (y*z=x ⊃ x=0+z*y)",
    hof"∀x ∀y1 ∀y2 ∀z x + y1*z + y2*z = x + (y1+y2)*z"
  ).flatMap( CNFp( _ ) ).foreach( ctx += _ )

  //Definitions
  ctx += "set_1" -> le" λk λl l = k"
  ctx += "ν" -> le" λk λl λm ∃n m = k + n*l"
  ctx += "U" -> le" λk λl λm ∃i ((i < l ∧ ¬i = k ) ∧ ν(i,l,m))"
  ctx += "DIV" -> le" λl λk ∃m l *m = k"
  ctx += "PRIME" -> le" λk (1 < k ∧ ∀l(DIV(l,k) -> (l = 1 ∨ l = k)))"
  ctx += "PRE" -> fof" ∀k (0 < k -> ∃m k = m+1)"
  ctx += "REM" -> hof" ∀l (0 < l -> ∀m∃k (k < l ∧ ν(k,l)(m) ))"
  ctx += "PRIME-DIV" -> hof" ∀m ((¬ m = 1) -> ∃l(PRIME l ∧ DIV l m) )"
  ctx += "subset" -> le" λX λY ∀n (X(n) -> Y(n))"
  ctx += "empty" -> le" λX ¬∃n X(n)"
  ctx += "compN" -> le" λX λx ¬X(x)"
  ctx += "union" -> le" λX λY λx (X(x) ∨ Y(x))"
  ctx += "intersection" -> le" λX λY λx (X(x) ∧ Y(x))"
  ctx += "O" -> le" λX ∀m (X(m) -> ∃l subset(ν(m, l+1), X))"
  ctx += "C" -> le" λX O(compN(X))"
  ctx += "INF" -> le" λX ∀k ∃l X(k+(l + 1))"

  // Definitions that depend on k
  val p = for ( i <- 0 to k )
    yield FOLConst( s"p_$i" )

  for ( c <- p ) ctx += c

  def F( k: Int ) = Const( s"F[$k]", To )
  def S( k: Int ) = Const( s"S[$k]", Ti -> To )
  def P( k: Int ) = Const( s"P[$k]", Ti -> To )
  def Q( k: Int ) = Const( s"Q[$k]", To )
  def R( k: Int ) = Const( s"R[$k]", To )
  def prod( k: Int ) = Const( s"prod[$k]", Ti )

  ctx += ( "P[0]", le" set_1(p_0)" )
  ctx += ( "S[0]", le" ν(0, p_0)" )
  ctx += ( "Q[0]", hof" PRIME(${p( 0 )})" )
  ctx += ( "R[0]", hof" ∀y (${P( 0 )}(y) -> PRIME y)" )
  ctx += hof"${prod( 0 )} = ${p( 0 )}"

  for ( i <- 1 to k ) {
    ctx += ( s"P[$i]", le"union(${P( i - 1 )}, set_1 (${p( i )}:i))" )
    ctx += ( s"S[$i]", le"union(${S( i - 1 )}, ν(0, ${p( i )}))" )
    ctx += ( s"Q[$i]", hof" ${Q( i - 1 )} ∧ PRIME(${p( i )})" )
    ctx += ( s"R[$i]", hof" ∀y (${P( i )} y -> PRIME y)" )
    ctx += hof"${prod( i )} = ${prod( i - 1 )} * ${p( i )}"
  }

  ctx += ( s"F[$k]", hof" ∀l (PRIME(l) <-> ${P( k )}(l))" )
}
