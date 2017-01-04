package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.ResolutionProofBuilder
import at.logic.gapt.proofs.{ Ant, Clause, Sequent, Suc }
import at.logic.gapt.utils.SatMatchers
import org.specs2.mutable._

class ResolutionTest extends Specification with SatMatchers {

  "Input" in {
    Input( Clause() ).conclusion.isEmpty must_== true
    Input( Clause() ).immediateSubProofs must beEmpty
    Input( hoa"P" +: Clause() ).mainIndices must_== Seq( Ant( 0 ) )
  }

  "ReflexivityClause" in {
    Refl( le"c" ).conclusion must_== ( Clause() :+ Eq( le"c", le"c" ) )
  }

  "TautologyClause" in {
    Taut( hoa"a" ).conclusion must_== ( hoa"a" +: Clause() :+ hoa"a" )
  }

  "Factor" in {
    Factor( Input( hoa"f(x)" +: hoa"f(x)" +: Clause() ), Ant( 0 ), Ant( 1 ) ).conclusion must_== ( hoa"f(x)" +: Clause() )
    Factor( Input( hoa"f(x)" +: hoa"f(x)" +: Clause() ), Ant( 1 ), Ant( 0 ) ) must throwAn[IllegalArgumentException]
    Factor( Input( hoa"f(x)" +: hoa"f(x)" +: Clause() ), Ant( 0 ), Ant( 2 ) ) must throwAn[IndexOutOfBoundsException]
    Factor( Input( hoa"f(x)" +: hoa"f(x)" +: Clause() :+ hoa"f(x)" ), Ant( 0 ), Suc( 0 ) ) must throwAn[IllegalArgumentException]
    Factor( Input( hoa"f(x)" +: hoa"f(y)" +: Clause() ), Ant( 0 ), Ant( 1 ) ) must throwAn[IllegalArgumentException]
  }

  "Factor companion" in {
    Factor( Input( hoa"f(x)" +: hoa"f(x)" +: Clause() ) ).conclusion must_== ( hoa"f(x)" +: Clause() )
  }

  "Resolution" in {
    Resolution(
      Input( Clause() :+ hoa"f(x)" ), Suc( 0 ),
      Input( hoa"f(x)" +: Clause() ), Ant( 0 )
    ).conclusion must_== Clause()

    Resolution(
      Input( Clause() :+ hoa"f(x)" ), Suc( 0 ),
      Input( hoa"f(y)" +: Clause() ), Ant( 0 )
    ) must throwAn[IllegalArgumentException]

    Resolution(
      Input( hoa"f(x)" +: Clause() ), Ant( 0 ),
      Input( Clause() :+ hoa"f(x)" ), Suc( 0 )
    ) must throwAn[IllegalArgumentException]

    Resolution(
      Input( hoa"a" +: Clause() :+ hoa"f(x)" :+ hoa"b" ), Suc( 0 ),
      Input( hoa"c" +: hoa"f(x)" +: Clause() :+ hoa"d" ), Ant( 1 )
    ).conclusion must_== ( hoa"a" +: hoa"c" +: Clause() :+ hoa"b" :+ hoa"d" )
  }

  "Paramod" in {
    Paramod(
      Input( Clause() :+ hoa"f(c) = g(d)" ), Suc( 0 ), true,
      Input( hoa"a" +: Clause() :+ hoa"p(f(c), f(c))" ), Suc( 0 ),
      le"λx p(f(c),x): o".asInstanceOf[Abs]
    ).conclusion must_== ( hoa"a" +: Clause() :+ hoa"p(f(c), g(d))" )
    Paramod(
      Input( Clause() :+ hoa"f(c) = g(d)" ), Suc( 0 ), true,
      Input( hoa"a" +: Clause() :+ hoa"p(f(c), f(c))" ), Suc( 0 ),
      le"λx p(x,x): o".asInstanceOf[Abs]
    ).conclusion must_== ( hoa"a" +: Clause() :+ hoa"p(g(d), g(d))" )
    Paramod(
      Input( Clause() :+ hoa"f(c) = g(d)" ), Suc( 0 ), true,
      Input( hoa"p(f(c), f(c))" +: Clause() ), Ant( 0 ),
      le"λx p(f(c),x): o".asInstanceOf[Abs]
    ).conclusion must_== ( hoa"p(f(c), g(d))" +: Clause() )
    Paramod(
      Input( Clause() :+ hoa"f(c) = g(d)" ), Suc( 0 ), false,
      Input( hoa"p(g(d), f(c))" +: Clause() ), Ant( 0 ),
      le"λx p(x,f(c)): o".asInstanceOf[Abs]
    ).conclusion must_== ( hoa"p(f(c), f(c))" +: Clause() )
  }

  "Paramod companion" in {
    Paramod(
      Input( Clause() :+ hoa"f(c) = g(d)" ), Suc( 0 ), true,
      Input( hoa"a" +: Clause() :+ hoa"p(f(c), f(c))" ), Suc( 0 ),
      le"^x p(f(c), x):o"
    ).conclusion must_== ( hoa"a" +: Clause() :+ hoa"p(f(c), g(d))" )
  }

  "Splitting" in {
    val in = Input( hof"!x!y (p x | q y) -> p c | q d" +: Sequent() )
    val c1 = ResolutionProofBuilder.c( in ).
      u( ImpL1( _, Ant( 0 ) ) ).
      u( AllR( _, Suc( 0 ), hov"x" ) ).
      u( AllR( _, Suc( 0 ), hov"y" ) ).
      u( OrR( _, Suc( 0 ) ) ).qed
    val c2 = ResolutionProofBuilder.c( in ).
      u( ImpL2( _, Ant( 0 ) ) ).u( OrL1( _, Ant( 0 ) ) ).qed
    val c3 = ResolutionProofBuilder.c( in ).
      u( ImpL2( _, Ant( 0 ) ) ).u( OrL2( _, Ant( 0 ) ) ).qed

    val comp1 = AvatarNonGroundComp( hoa"spl1", hof"!x p x", Seq( hov"x" ) )
    val comp2 = AvatarNonGroundComp( hoa"spl2", hof"!x q x", Seq( hov"y" ) )
    val split = AvatarSplit( c1, Seq( comp1, comp2 ) )

    val p1 = AvatarComponent( comp1 )
    val p2 = AvatarComponent( comp2.copy( vars = Seq( hov"x" ) ) )

    val case1 = AvatarContradiction( Resolution( Subst( p1, Substitution( hov"x" -> le"c" ) ), Suc( 0 ), c2, Ant( 0 ) ) )
    val case2 = AvatarContradiction( Resolution( Subst( p2, Substitution( hov"x" -> le"d" ) ), Suc( 0 ), c3, Ant( 0 ) ) )
    val proof = Resolution( Resolution( AvatarContradiction( split ), Suc( 0 ), case1, Ant( 0 ) ), Suc( 0 ), case2, Ant( 0 ) )
    proof.isProof must_== true

    ResolutionToExpansionProof.withDefs( proof ).deep must beValidSequent
    val expansion = ResolutionToExpansionProof( proof )
    expansion.deep must beValidSequent
    val Some( resFromExp ) = ExpansionToResolutionProof( expansion )
    resFromExp.isProof must_== true

    val lk = ResolutionToLKProof( proof )
    lk.endSequent must_== in.sequent.swapped
  }

  "daglike performance" in {
    def proof( n: Int ) = {
      var p: ResolutionProof = Taut( hoa"a" )
      0 until n foreach { i =>
        p = Resolution( p, Suc( 0 ), p, Ant( 0 ) )
      }
      p
    }

    val n = 10000
    val copy1 = proof( n )
    val copy2 = proof( n )

    copy1 == copy2 must_== true
  }

}
