package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Suc, Ant, Clause }
import org.specs2.mutable._

class ResolutionTest extends Specification {

  "InputClause" in {
    InputClause( Clause() ).conclusion.isEmpty must_== true
    InputClause( Clause() ).immediateSubProofs must beEmpty
    InputClause( hoa"P" +: Clause() ).mainIndices must_== Seq( Ant( 0 ) )
  }

  "ReflexivityClause" in {
    ReflexivityClause( le"c" ).conclusion must_== ( Clause() :+ Eq( le"c", le"c" ) )
  }

  "TautologyClause" in {
    TautologyClause( hoa"a" ).conclusion must_== ( hoa"a" +: Clause() :+ hoa"a" )
  }

  "Factor" in {
    Factor( InputClause( hoa"f(x)" +: hoa"f(x)" +: Clause() ), Ant( 0 ), Ant( 1 ) ).conclusion must_== ( hoa"f(x)" +: Clause() )
    Factor( InputClause( hoa"f(x)" +: hoa"f(x)" +: Clause() ), Ant( 1 ), Ant( 0 ) ) must throwAn[IllegalArgumentException]
    Factor( InputClause( hoa"f(x)" +: hoa"f(x)" +: Clause() ), Ant( 0 ), Ant( 2 ) ) must throwAn[IndexOutOfBoundsException]
    Factor( InputClause( hoa"f(x)" +: hoa"f(x)" +: Clause() :+ hoa"f(x)" ), Ant( 0 ), Suc( 0 ) ) must throwAn[IllegalArgumentException]
    Factor( InputClause( hoa"f(x)" +: hoa"f(y)" +: Clause() ), Ant( 0 ), Ant( 1 ) ) must throwAn[IllegalArgumentException]
  }

  "Factor companion" in {
    Factor( InputClause( hoa"f(x)" +: hoa"f(x)" +: Clause() ) )._1.conclusion must_== ( hoa"f(x)" +: Clause() )
  }

  "Resolution" in {
    Resolution(
      InputClause( Clause() :+ hoa"f(x)" ), Suc( 0 ),
      InputClause( hoa"f(x)" +: Clause() ), Ant( 0 )
    ).conclusion must_== Clause()

    Resolution(
      InputClause( Clause() :+ hoa"f(x)" ), Suc( 0 ),
      InputClause( hoa"f(y)" +: Clause() ), Ant( 0 )
    ) must throwAn[IllegalArgumentException]

    Resolution(
      InputClause( hoa"f(x)" +: Clause() ), Ant( 0 ),
      InputClause( Clause() :+ hoa"f(x)" ), Suc( 0 )
    ) must throwAn[IllegalArgumentException]

    Resolution(
      InputClause( hoa"a" +: Clause() :+ hoa"f(x)" :+ hoa"b" ), Suc( 0 ),
      InputClause( hoa"c" +: hoa"f(x)" +: Clause() :+ hoa"d" ), Ant( 1 )
    ).conclusion must_== ( hoa"a" +: hoa"c" +: Clause() :+ hoa"b" :+ hoa"d" )
  }

  "Paramodulation" in {
    Paramodulation(
      InputClause( Clause() :+ hoa"f(c) = g(d)" ), Suc( 0 ),
      InputClause( hoa"a" +: Clause() :+ hoa"p(f(c), f(c))" ), Suc( 0 ),
      le"λx p(f(c),x): o".asInstanceOf[Abs], leftToRight = true
    ).conclusion must_== ( hoa"a" +: Clause() :+ hoa"p(f(c), g(d))" )
    Paramodulation(
      InputClause( Clause() :+ hoa"f(c) = g(d)" ), Suc( 0 ),
      InputClause( hoa"a" +: Clause() :+ hoa"p(f(c), f(c))" ), Suc( 0 ),
      le"λx p(x,x): o".asInstanceOf[Abs], leftToRight = true
    ).conclusion must_== ( hoa"a" +: Clause() :+ hoa"p(g(d), g(d))" )
    Paramodulation(
      InputClause( Clause() :+ hoa"f(c) = g(d)" ), Suc( 0 ),
      InputClause( hoa"p(f(c), f(c))" +: Clause() ), Ant( 0 ),
      le"λx p(f(c),x): o".asInstanceOf[Abs], leftToRight = true
    ).conclusion must_== ( hoa"p(f(c), g(d))" +: Clause() )
    Paramodulation(
      InputClause( Clause() :+ hoa"f(c) = g(d)" ), Suc( 0 ),
      InputClause( hoa"p(g(d), f(c))" +: Clause() ), Ant( 0 ),
      le"λx p(x,f(c)): o".asInstanceOf[Abs], leftToRight = false
    ).conclusion must_== ( hoa"p(f(c), f(c))" +: Clause() )
  }

  "Paramodulation companion" in {
    Paramodulation(
      InputClause( Clause() :+ hoa"f(c) = g(d)" ), Suc( 0 ),
      InputClause( hoa"a" +: Clause() :+ hoa"p(f(c), f(c))" ), Suc( 0 ),
      hoa"p(f(c), g(d))"
    ).conclusion must_== ( hoa"a" +: Clause() :+ hoa"p(f(c), g(d))" )
  }

  "Splitting" in {
    val c1 = InputClause( Clause() :+ hoa"p" :+ hoa"q" )
    val c2 = InputClause( hoa"p" +: Clause() )
    val c3 = InputClause( hoa"q" +: Clause() )

    val splCls = c1
    val case1 = Resolution( InputClause( Clause() :+ hoa"p" ), Suc( 0 ), c2, Ant( 0 ) )
    val case2 = Resolution( InputClause( Clause() :+ hoa"q" ), Suc( 0 ), c3, Ant( 0 ) )
    val proof = Splitting( splCls, Clause() :+ hoa"p", Clause() :+ hoa"q", case1, case2 )
    proof.conclusion must beEmpty
  }

  "daglike performance" in {
    def proof( n: Int ) = {
      var p: ResolutionProof = TautologyClause( hoa"a" )
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
