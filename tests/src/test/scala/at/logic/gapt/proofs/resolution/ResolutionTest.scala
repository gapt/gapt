package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Suc, Ant, Clause }
import org.specs2.mutable._

class ResolutionTest extends Specification {

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

  //  "Splitting" in {
  //    val c1 = Input( Clause() :+ hoa"p" :+ hoa"q" )
  //    val c2 = Input( hoa"p" +: Clause() )
  //    val c3 = Input( hoa"q" +: Clause() )
  //
  //    val splCls = c1
  //    val case1 = Resolution( Input( Clause() :+ hoa"p" ), Suc( 0 ), c2, Ant( 0 ) )
  //    val case2 = Resolution( Input( Clause() :+ hoa"q" ), Suc( 0 ), c3, Ant( 0 ) )
  //    val proof = Splitting( splCls, Clause() :+ hoa"p", Clause() :+ hoa"q", case1, case2 )
  //    proof.conclusion must beEmpty
  //  }

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
