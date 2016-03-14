package at.logic.gapt.proofs.reduction

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.resolution.{ InputClause, MguResolution }
import org.specs2.mutable._

class ErasureReductionTest extends Specification {
  "two-sorted" in {
    implicit var ctx = FiniteContext()
    ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
    ctx += Context.Sort( "witness" )
    ctx += hoc"f: witness > witness"
    ctx += hoc"P: nat > witness > o"
    ctx += hoc"Q: nat > o"

    val red = new ErasureReductionHelper( ctx.constants )

    val c1 = Clause() :+ hoa"P 0 y"
    val c2 = hoa"P x (f y)" +: Clause() :+ hoa"P (s x) y"
    val c3 = hoa"P x y" +: Clause() :+ hoa"Q x"
    val c4 = hoa"Q (s (s (s (s 0))))" +: Clause()

    val Seq( ec1, ec2, ec3, ec4 ) = Seq( c1, c2, c3, c4 ) map { red.forward }

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
