package at.logic.gapt.proofs.resolution

import at.logic.gapt.expr._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle
import at.logic.gapt.proofs.{ Suc, Ant, Clause }
import org.specs2.mutable._

class ResolutionTest extends Specification {

  "InputClause" in {
    InputClause( Clause() ).conclusion.isEmpty must_== true
    InputClause( Clause() ).immediateSubProofs must beEmpty
    InputClause( FOLAtom( "P" ) +: Clause() ).mainIndices must_== Seq( Ant( 0 ) )
  }

  "ReflexivityClause" in {
    val c = FOLFunction( "c" )
    ReflexivityClause( c ).conclusion must_== ( Clause() :+ Eq( c, c ) )
  }

  "TautologyClause" in {
    val a = FOLAtom( "a" )
    TautologyClause( a ).conclusion must_== ( a +: Clause() :+ a )
  }

  "Factor" in {
    val Seq( fx, fy ) = Seq( "x", "y" ) map { n => FOLAtom( "f", FOLVar( n ) ) }
    Factor( InputClause( fx +: fx +: Clause() ), Ant( 0 ), Ant( 1 ) ).conclusion must_== ( fx +: Clause() )
    Factor( InputClause( fx +: fx +: Clause() ), Ant( 1 ), Ant( 0 ) ) must throwAn[IllegalArgumentException]
    Factor( InputClause( fx +: fx +: Clause() ), Ant( 0 ), Ant( 2 ) ) must throwAn[IndexOutOfBoundsException]
    Factor( InputClause( fx +: fx +: Clause() :+ fx ), Ant( 0 ), Suc( 0 ) ) must throwAn[IllegalArgumentException]
    Factor( InputClause( fx +: fy +: Clause() ), Ant( 0 ), Ant( 1 ) ) must throwAn[IllegalArgumentException]
  }

  "Factor companion" in {
    val Seq( fx, fy ) = Seq( "x", "y" ) map { n => FOLAtom( "f", FOLVar( n ) ) }
    Factor( InputClause( fx +: fx +: Clause() ) )._1.conclusion must_== ( fx +: Clause() )
  }

  "Resolution" in {
    val Seq( fx, fy ) = Seq( "x", "y" ) map { n => FOLAtom( "f", FOLVar( n ) ) }

    Resolution(
      InputClause( Clause() :+ fx ), Suc( 0 ),
      InputClause( fx +: Clause() ), Ant( 0 )
    ).conclusion must_== Clause()

    Resolution(
      InputClause( Clause() :+ fx ), Suc( 0 ),
      InputClause( fy +: Clause() ), Ant( 0 )
    ) must throwAn[IllegalArgumentException]

    Resolution(
      InputClause( fx +: Clause() ), Ant( 0 ),
      InputClause( Clause() :+ fx ), Suc( 0 )
    ) must throwAn[IllegalArgumentException]

    Resolution(
      InputClause( FOLAtom( "a" ) +: Clause() :+ fx :+ FOLAtom( "b" ) ), Suc( 0 ),
      InputClause( FOLAtom( "c" ) +: fx +: Clause() :+ FOLAtom( "d" ) ), Ant( 1 )
    ).conclusion must_== ( "a" +: "c" +: Clause() :+ "b" :+ "d" map { FOLAtom( _ ) } )
  }

  def parseAtom( s: String ): FOLAtom = Prover9TermParserLadrStyle.parseFormula( s ).asInstanceOf[FOLAtom]

  "Paramodulation" in {
    Paramodulation(
      InputClause( Clause() :+ "f(c) = g(d)" map parseAtom ), Suc( 0 ),
      InputClause( "a" +: Clause() :+ "p(f(c), f(c))" map parseAtom ), Suc( 0 ),
      Seq( LambdaPosition( 2 ) ), leftToRight = true
    ).conclusion must_== ( "a" +: Clause() :+ "p(f(c), g(d))" map parseAtom )
    Paramodulation(
      InputClause( Clause() :+ "f(c) = g(d)" map parseAtom ), Suc( 0 ),
      InputClause( "a" +: Clause() :+ "p(f(c), f(c))" map parseAtom ), Suc( 0 ),
      Seq( LambdaPosition( 1, 2 ), LambdaPosition( 2 ) ), leftToRight = true
    ).conclusion must_== ( "a" +: Clause() :+ "p(g(d), g(d))" map parseAtom )
    Paramodulation(
      InputClause( Clause() :+ "f(c) = g(d)" map parseAtom ), Suc( 0 ),
      InputClause( "p(f(c), f(c))" +: Clause() map parseAtom ), Ant( 0 ),
      Seq( LambdaPosition( 2 ) ), leftToRight = true
    ).conclusion must_== ( "p(f(c), g(d))" +: Clause() map parseAtom )
    Paramodulation(
      InputClause( Clause() :+ "f(c) = g(d)" map parseAtom ), Suc( 0 ),
      InputClause( "p(g(d), f(c))" +: Clause() map parseAtom ), Ant( 0 ),
      Seq( LambdaPosition( 1, 2 ) ), leftToRight = false
    ).conclusion must_== ( "p(f(c), f(c))" +: Clause() map parseAtom )
  }

  "Paramodulation companion" in {
    Paramodulation(
      InputClause( Clause() :+ "f(c) = g(d)" map parseAtom ), Suc( 0 ),
      InputClause( "a" +: Clause() :+ "p(f(c), f(c))" map parseAtom ), Suc( 0 ),
      parseAtom( "p(f(c), g(d))" )
    ).conclusion must_== ( "a" +: Clause() :+ "p(f(c), g(d))" map parseAtom )
  }

  "daglike performance" in {
    def proof( n: Int ) = {
      var p: ResolutionProof = TautologyClause( FOLAtom( "a" ) )
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
