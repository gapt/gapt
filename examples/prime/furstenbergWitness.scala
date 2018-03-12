package gapt.examples.prime

import gapt.expr._
import gapt.proofs.ImmutableContext
import gapt.proofs.expansion.ETWeakQuantifier
import gapt.proofs.lk.{ LKToExpansionProof, eliminateDefinitions, skolemizeLK }
import gapt.proofs.lkt._

object furstenbergWitness {
  case class Multiset[T]( countingMap: Map[T, Int] = Map[T, Int]() ) extends ( T => Int ) {
    for ( ( _, v ) <- countingMap ) require( v > 0 )
    def apply( t: T ): Int = countingMap.getOrElse( t, 0 )
    def +( that: Multiset[T] ): Multiset[T] =
      Multiset( Map() ++
        ( this.countingMap.keySet union that.countingMap.keySet ).view.
        map( k => k -> ( this( k ) + that( k ) ) ) )

    def toSeq: Seq[T] =
      countingMap.view.flatMap {
        case ( t, n ) => List.fill( n )( t )
      }.toList

    override def toString(): String =
      countingMap.map {
        case ( k, 1 ) => k.toString
        case ( k, n ) => s"$k^$n"
      }.mkString( "{", ",", "}" )
  }
  case class ZZMPolynomial[V] private ( coeffsMap: Map[Multiset[V], Int] ) {
    def coeff( v: Multiset[V] ): Int = coeffsMap.getOrElse( v, 0 )
    def +( that: ZZMPolynomial[V] ): ZZMPolynomial[V] = ZZMPolynomial {
      for ( m <- this.coeffsMap.keySet union that.coeffsMap.keySet )
        yield m -> ( this.coeff( m ) + that.coeff( m ) )
    }
    def *( that: ZZMPolynomial[V] ): ZZMPolynomial[V] = ZZMPolynomial {
      for ( ( m1, c1 ) <- this.coeffsMap.view; ( m2, c2 ) <- that.coeffsMap.view )
        yield ( m1 + m2 ) -> ( c1 * c2 )
    }
  }
  object ZZMPolynomial {
    implicit def fromScalar[V]( n: Int ): ZZMPolynomial[V] =
      ZZMPolynomial( Map( Multiset[V]() -> n ) )
    implicit def fromVariable[V]( v: V ): ZZMPolynomial[V] =
      ZZMPolynomial( Map( Multiset[V]( Map( v -> 1 ) ) -> 1 ) )
    def apply[V]( coeffs: Iterable[( Multiset[V], Int )] ): ZZMPolynomial[V] =
      new ZZMPolynomial( ( Map() ++ coeffs.view.
        groupBy( _._1 ).
        mapValues( _.map( _._2 ).sum ) ).
        filter( _._2 != 0 ) )
  }

  def apply( n: Int ): ( Expr, ImmutableContext ) = {
    val primeInst = furstenberg( n )
    implicit val ctx = primeInst.ctx.newMutable
    val p0 = eliminateDefinitions( primeInst.proof )
    val ( p1, lctx ) = LKToLKt( p0 )
    val p2 = atomizeEquality( p1, lctx )
    val p3 = normalizeLKt( p2 )
    val p4 = LKtToLK( p3, lctx )

    ctx.addSkolemSym( le"λk_4 ∃m (k_4:nat) = ((m:nat) + (s(0:nat): nat): nat)", "pred" )
    ctx.addSkolemSym(
      le"""
        λm_12 ∃l ((s(0:nat): nat) < (l:nat) ∧
         ∀l_0 (∃m ((l_0:nat) * (m:nat): nat) = l →
          l_0 = s(0) ∨ l_0 = l) ∧ ∃m_0 l * m_0 = (m_12:nat))
        """,
      "primediv_of" )

    val p5 = skolemizeLK( p4, proofTheoretic = false )
    val p6 = LKToExpansionProof( p5 )
    val Some( Seq( witness ) ) = p6.expansionSequent.antecedent.collectFirst {
      case ETWeakQuantifier( All( _, Iff( _, _ ) ), insts ) =>
        insts.keys.toSeq.filter {
          case App( Const( "p", _, _ ), _ ) => false
          case _                            => true
        }
    }

    def toMPolynomial( e: Expr ): ZZMPolynomial[Expr] =
      e match {
        case App( Const( "p", _, _ ), _ ) => e
        case Apps( Const( "*", _, _ ), Seq( a, b ) ) =>
          toMPolynomial( a ) * toMPolynomial( b )
        case Apps( Const( "+", _, _ ), Seq( a, b ) ) =>
          toMPolynomial( a ) + toMPolynomial( b )
        case Apps( Const( "pred", _, _ ), Seq( a ) ) =>
          toMPolynomial( a ) + ( -1 )
        case Apps( Const( "s", _, _ ), Seq( a ) ) =>
          toMPolynomial( a ) + 1
        case Const( "0", _, _ ) => 0
      }
    def toExprN( n: Int ): Expr =
      if ( n == 0 ) le"0"
      else if ( n < 0 ) le"pred ${toExprN( n + 1 )}"
      else le"s ${toExprN( n - 1 )}"
    def toExprM( m: Multiset[Expr] ): Expr =
      m.toSeq.reduceOption( ( a, b ) => le"$a * $b" ).getOrElse( le"s(0)" )
    def toExprP( p: ZZMPolynomial[Expr] ): Expr =
      p.coeffsMap.map {
        case ( mon, 1 ) => toExprM( mon )
        case ( mon, v ) => le"${toExprN( v )} * ${toExprM( mon )}"
      }.reduceOption( ( a, b ) => le"$a + $b" ).getOrElse( le"0" )

    val witness2 = witness match {
      case App( c @ Const( "primediv_of", _, _ ), arg ) =>
        App( c, toExprP( toMPolynomial( arg ) ) )
    }

    ( witness2, ctx.toImmutable )
  }
}
