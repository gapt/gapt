package at.logic.gapt.proofs.reduction

import at.logic.gapt.expr._
import at.logic.gapt.proofs.resolution.{ InputClause, MguResolution }
import at.logic.gapt.proofs.{ Ant, Suc, Clause }
import org.specs2.mutable._

class ErasureReductionTest extends Specification {
  "two-sorted" in {
    val nat = TBase( "nat" )
    val witness = TBase( "witness" )

    val o = Const( "0", nat )
    val s = Const( "s", nat -> nat )

    val f = Const( "f", witness -> witness )

    val P = HOLAtomConst( "P", nat, witness )
    val Q = HOLAtomConst( "Q", nat )

    val x = Var( "x", nat )
    val y = Var( "y", witness )

    val red = ErasureReduction( Set( o, s, f, P, Q ) )

    val c1 = Clause() :+ P( o, y )
    val c2 = P( x, f( y ) ) +: Clause() :+ P( s( x ), y )
    val c3 = P( x, y ) +: Clause() :+ Q( x )
    val c4 = Q( s( s( s( s( o ) ) ) ) ) +: Clause()

    val Seq( ec1, ec2, ec3, ec4 ) = Seq( c1, c2, c3, c4 ) map { red forward }

    val p1 = InputClause( ec2 )
    val p2 = MguResolution( p1, Suc( 0 ), p1, Ant( 0 ) )
    val p3 = MguResolution( p2, Suc( 0 ), p2, Ant( 0 ) )
    val p4 = MguResolution( InputClause( ec1 ), Suc( 0 ), p3, Ant( 0 ) )
    val p5 = MguResolution( InputClause( ec3 ), Suc( 0 ), InputClause( ec4 ), Ant( 0 ) )
    val p6 = MguResolution( p4, Suc( 0 ), p5, Ant( 0 ) )

    p6.conclusion must_== Clause()

    val reifiedProof = red.back( p6, Set( c1, c2, c3, c4 ) )
    println( reifiedProof )
    reifiedProof.conclusion must_== Clause()
  }
}
