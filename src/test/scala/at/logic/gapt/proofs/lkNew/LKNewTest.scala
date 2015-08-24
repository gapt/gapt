package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.proofs.lk.base._
import org.specs2.execute.Success
import org.specs2.mutable._

/**
 * Created by sebastian on 8/6/15.
 */
class LKNewTest extends Specification {
  val c = FOLConst( "c" )
  val d = FOLConst( "d" )
  val alpha = FOLVar( "α" )
  val x = FOLVar( "x" )
  val y = FOLVar( "y" )

  def P( t: FOLTerm ) = FOLAtom( "P", t )

  val A = FOLAtom( "A", Nil )
  val B = FOLAtom( "B", Nil )
  val C = FOLAtom( "C", Nil )
  val D = FOLAtom( "D", Nil )
  val E = FOLAtom( "E", Nil )
  val F = FOLAtom( "F", Nil )

  val Pc = FOLAtom( "P", c )
  val Pd = FOLAtom( "P", d )

  private def testParents( o: OccConnector, ruleName: String )( sequent: HOLSequent, parents: Seq[SequentIndex]* ): Success = {
    val ( m, n ) = sequent.sizes
    for ( ( i, ps ) <- sequent.indices zip parents ) {
      o.parents( i ) aka s"$ruleName: Parents of $i in $sequent should be $ps" must beEqualTo( ps )
    }
    o.parents( Ant( m ) ) aka s"Parents of ${Ant( m )} in $sequent" must throwAn[IndexOutOfBoundsException]
    o.parents( Suc( n ) ) aka s"Parents of ${Suc( n )} in $sequent" must throwAn[IndexOutOfBoundsException]
    success
  }

  private def testChildren( o: OccConnector, ruleName: String )( sequent: HOLSequent, children: Seq[SequentIndex]* ): Success = {
    val ( m, n ) = sequent.sizes
    for ( ( i, cs ) <- sequent.indices zip children ) {
      o.children( i ) aka s"$ruleName: Children of $i in $sequent should be $cs" must beEqualTo( cs )
    }

    o.children( Ant( m ) ) aka s"Parents of ${Ant( m )} in $sequent" must throwAn[IndexOutOfBoundsException]
    o.children( Suc( n ) ) aka s"Parents of ${Suc( n )} in $sequent" must throwAn[IndexOutOfBoundsException]
    success
  }

  "LogicalAxiom" should {
    "correctly create an axiom" in {
      LogicalAxiom( A )

      success
    }

    "correctly return its main formula" in {
      val ax = LogicalAxiom( A )

      if ( ax.mainIndices.length != 2 )
        failure

      val ( i1, i2 ) = ( ax.mainIndices.head, ax.mainIndices.tail.head )
      ax.endSequent( i1 ) must beEqualTo( A )
      ax.endSequent( i2 ) must beEqualTo( A )
    }
  }

  "ReflexivityAxiom" should {
    "correctly create an axiom" in {
      ReflexivityAxiom( c )

      success
    }

    "correctly return its main formula" in {
      val ax = ReflexivityAxiom( c )

      if ( ax.mainIndices.length != 1 )
        failure

      val i = ax.mainIndices.head
      ax.endSequent( i ) must beEqualTo( Eq( c, c ) )
    }
  }

  "WeakeningLeftRule" should {
    "correctly create a proof" in {
      WeakeningLeftRule( LogicalAxiom( A ), Pc )

      success
    }

    "correctly return its main formula" in {
      val p = WeakeningLeftRule( LogicalAxiom( A ), Pc )

      if ( p.mainIndices.length != 1 )
        failure

      val i = p.mainIndices.head

      p.endSequent( i ) must beEqualTo( Pc )
    }

    "correctly connect occurrences" in {
      //end sequent of p: B, A :- A
      val p = WeakeningLeftRule( LogicalAxiom( A ), B )

      val o = p.getOccConnector

      testChildren( o, "w_l" )(
        p.premise,
        Seq( Ant( 1 ) ),

        Seq( Suc( 0 ) )
      )

      testParents( o, "w_l" )(
        p.endSequent,
        Seq(),
        Seq( Ant( 0 ) ),
        Seq( Suc( 0 ) )
      )
    }
  }

  "WeakeningRightRule" should {
    "correctly create a proof" in {
      WeakeningRightRule( LogicalAxiom( A ), B )

      success
    }

    "correctly return its main formula" in {
      val p = WeakeningRightRule( LogicalAxiom( A ), B )

      if ( p.mainIndices.length != 1 )
        failure

      val i = p.mainIndices.head

      p.endSequent( i ) must beEqualTo( B )
    }

    "correctly connect occurrences" in {
      // end sequent of p: A :- A, B
      val p = WeakeningRightRule( LogicalAxiom( A ), B )

      val o = p.getOccConnector

      testChildren( o, "w_r" )(
        p.endSequent,
        Seq( Ant( 0 ) ),
        Seq( Suc( 0 ) )
      )

      testParents( o, "w_r" )(
        p.endSequent,
        Seq( Ant( 0 ) ),
        Seq( Suc( 0 ) ),
        Seq()
      )
    }
  }

  "ContractionLeftRule" should {

    "correctly create a proof" in {
      ContractionLeftRule( WeakeningLeftRule( LogicalAxiom( A ), A ), Ant( 0 ), Ant( 1 ) )
      ContractionLeftRule( WeakeningLeftRule( LogicalAxiom( A ), A ), A )

      success
    }

    "refuse to construct a proof" in {
      ContractionLeftRule( LogicalAxiom( A ), Ant( 0 ), Ant( 1 ) ) must throwAn[LKRuleCreationException]
      ContractionLeftRule( WeakeningLeftRule( LogicalAxiom( A ), Pc ), Ant( 0 ), Ant( 1 ) ) must throwAn[LKRuleCreationException]
      ContractionLeftRule( LogicalAxiom( A ), Ant( 0 ), Ant( 0 ) ) must throwAn[LKRuleCreationException]
      ContractionLeftRule( LogicalAxiom( Pc ), A ) must throwAn[LKRuleCreationException]
      ContractionLeftRule( LogicalAxiom( A ), A ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val p = ContractionLeftRule( WeakeningLeftRule( LogicalAxiom( A ), A ), A )

      if ( p.mainIndices.length != 1 )
        failure

      val i = p.mainIndices.head

      p.endSequent( i ) must beEqualTo( A )
    }

    "correctly return its aux formulas" in {
      val p = ContractionLeftRule( WeakeningLeftRule( LogicalAxiom( A ), A ), A )

      if ( p.auxIndices.length != 1 )
        failure
      if ( p.auxIndices.head.length != 2 )
        failure

      for ( i <- p.auxIndices.head ) {
        p.premise( i ) must beEqualTo( A )
      }
      success
    }

    "correctly connect occurrences" in {
      // end sequent of p: A, B, C :- A, B
      val p = ContractionLeftRule( ArbitraryAxiom( B +: A +: C +: A +: Sequent() :+ A :+ B ), A )

      val o = p.getOccConnector

      testParents( o, "c_l" )(
        p.endSequent,
        Seq( Ant( 1 ), Ant( 3 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),
        Seq( Suc( 0 ) ),
        Seq( Suc( 1 ) )
      )

      testChildren( o, "c_l" )(
        p.premise,
        Seq( Ant( 1 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),
        Seq( Ant( 0 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 1 ) )
      )
    }
  }

  "ContractionRightRule" should {

    "correctly create a proof" in {
      ContractionRightRule( WeakeningRightRule( LogicalAxiom( A ), A ), Suc( 0 ), Suc( 1 ) )
      ContractionRightRule( WeakeningRightRule( LogicalAxiom( A ), A ), A )

      success
    }

    "refuse to construct a proof" in {
      ContractionRightRule( LogicalAxiom( A ), Suc( 0 ), Suc( 1 ) ) must throwAn[LKRuleCreationException]
      ContractionRightRule( WeakeningRightRule( LogicalAxiom( A ), Pc ), Suc( 0 ), Suc( 1 ) ) must throwAn[LKRuleCreationException]
      ContractionRightRule( LogicalAxiom( A ), Suc( 0 ), Suc( 0 ) ) must throwAn[LKRuleCreationException]
      ContractionRightRule( LogicalAxiom( Pc ), A ) must throwAn[LKRuleCreationException]
      ContractionRightRule( LogicalAxiom( A ), A ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val p = ContractionRightRule( WeakeningRightRule( LogicalAxiom( A ), A ), A )

      if ( p.mainIndices.length != 1 )
        failure

      val i = p.mainIndices.head

      p.endSequent( i ) must beEqualTo( A )
    }

    "correctly return its aux formulas" in {
      val p = ContractionRightRule( WeakeningRightRule( LogicalAxiom( A ), A ), A )

      if ( p.auxIndices.length != 1 )
        failure
      if ( p.auxIndices.head.length != 2 )
        failure

      for ( i <- p.auxIndices.head ) {
        p.premise( i ) must beEqualTo( A )
      }
      success
    }

    "correctly connect occurrences" in {
      // end sequent of p: A, B :- B, C, A
      val p = ContractionRightRule( ArbitraryAxiom( A +: B +: Sequent() :+ A :+ B :+ A :+ C ), Suc( 0 ), Suc( 2 ) )

      val o = p.getOccConnector

      testParents( o, "c_r" )(
        p.endSequent,
        Seq( Ant( 0 ) ),
        Seq( Ant( 1 ) ),

        Seq( Suc( 1 ) ),
        Seq( Suc( 3 ) ),
        Seq( Suc( 0 ), Suc( 2 ) )
      )

      testChildren( o, "c_r" )(
        p.premise,
        Seq( Ant( 0 ) ),
        Seq( Ant( 1 ) ),

        Seq( Suc( 2 ) ),
        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Suc( 1 ) )
      )
    }
  }

  "CutRule" should {
    "correctly produce a proof" in {
      CutRule( ArbitraryAxiom( A +: B +: Sequent() :+ B ), Suc( 0 ), LogicalAxiom( B ), Ant( 0 ) )
      CutRule( ArbitraryAxiom( A +: B +: Sequent() :+ B ), LogicalAxiom( B ), B )

      success
    }

    "refuse to produce a proof" in {
      val p1 = ArbitraryAxiom( Sequent() :+ A :+ B )
      val p2 = ArbitraryAxiom( C +: B +: Sequent() )

      CutRule( p1, Ant( 0 ), p2, Ant( 0 ) ) must throwAn[LKRuleCreationException]
      CutRule( p1, Suc( 0 ), p2, Suc( 0 ) ) must throwAn[LKRuleCreationException]
      CutRule( p1, Suc( 0 ), p2, Ant( 0 ) ) must throwAn[LKRuleCreationException]
      CutRule( p1, Suc( 2 ), p2, Ant( 0 ) ) must throwAn[LKRuleCreationException]
      CutRule( p1, Suc( 0 ), p2, Ant( 3 ) ) must throwAn[LKRuleCreationException]
    }

    "correctly return its aux formulas" in {
      val p1 = ArbitraryAxiom( Sequent() :+ A :+ B )
      val p2 = ArbitraryAxiom( C +: B +: Sequent() )

      val p = CutRule( p1, p2, B )
      if ( p.auxIndices.length != 2 )
        failure
      if ( ( p.auxIndices.head.length != 1 ) || ( p.auxIndices.tail.head.length != 1 ) )
        failure

      val ( i, j ) = ( p.auxIndices.head.head, p.auxIndices.tail.head.head )

      p.leftPremise( i ) must beEqualTo( B )
      p.rightPremise( j ) must beEqualTo( B )
    }

    "correctly connect occurrences" in {
      val p1 = ArbitraryAxiom( A +: B +: Sequent() :+ A :+ B :+ C )
      val p2 = ArbitraryAxiom( D +: B +: E +: F +: Sequent() :+ B :+ E )

      // end sequent of p: A, B, D, E, F :- A, C, B, E
      val p = CutRule( p1, p2, B )
      val oL = p.getLeftOccConnector
      val oR = p.getRightOccConnector

      testChildren( oL, "cut" )(
        p.leftPremise,
        Seq( Ant( 0 ) ),
        Seq( Ant( 1 ) ),

        Seq( Suc( 0 ) ),
        Seq(),
        Seq( Suc( 1 ) )
      )

      testParents( oL, "cut" )(
        p.endSequent,
        Seq( Ant( 0 ) ),
        Seq( Ant( 1 ) ),
        Seq(),
        Seq(),
        Seq(),

        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq(),
        Seq()
      )

      testChildren( oR, "cut" )(
        p.rightPremise,
        Seq( Ant( 2 ) ),
        Seq(),
        Seq( Ant( 3 ) ),
        Seq( Ant( 4 ) ),

        Seq( Suc( 2 ) ),
        Seq( Suc( 3 ) )
      )

      testParents( oR, "cut" )(
        p.endSequent,
        Seq(),
        Seq(),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),
        Seq( Ant( 3 ) ),

        Seq(),
        Seq(),
        Seq( Suc( 0 ) ),
        Seq( Suc( 1 ) )
      )
    }
  }

  "NegLeftRule" should {

    "correctly create a proof" in {
      NegLeftRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D ), Suc( 0 ) )
      NegLeftRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D ), C )

      success
    }

    "refuse to create a proof" in {
      NegLeftRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D ), Ant( 0 ) ) must throwAn[LKRuleCreationException]
      NegLeftRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D ), Suc( 2 ) ) must throwAn[LKRuleCreationException]
      NegLeftRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D ), A ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val p = NegLeftRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D ), C )

      if ( p.mainIndices.length != 1 )
        failure

      val i = p.mainIndices.head

      p.endSequent( i ) must beEqualTo( Neg( C ) )
    }

    "correctly return its aux formulas" in {
      val p = NegLeftRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D :+ E ), C )

      if ( p.auxIndices.length != 1 )
        failure
      if ( p.auxIndices.head.length != 1 )
        failure

      for ( i <- p.auxIndices.head ) {
        p.premise( i ) must beEqualTo( C )
      }
      success
    }

    "correctly connect occurrences" in {
      // end sequent of p: ¬D, A, B :- C, E
      val p = NegLeftRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D :+ E ), D )

      val o = p.getOccConnector

      testChildren( o, "¬:l" )(
        p.premise,
        Seq( Ant( 1 ) ),
        Seq( Ant( 2 ) ),

        Seq( Suc( 0 ) ),
        Seq( Ant( 0 ) ),
        Seq( Suc( 1 ) )
      )

      testParents( o, "¬:l" )(
        p.endSequent,
        Seq( Suc( 1 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 1 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) )
      )
    }
  }

  "NegRightRule" should {

    "correctly create a proof" in {
      NegRightRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D ), Ant( 0 ) )
      NegRightRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D ), A )

      success
    }

    "refuse to create a proof" in {
      NegRightRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D ), Suc( 0 ) ) must throwAn[LKRuleCreationException]
      NegRightRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D ), Ant( 2 ) ) must throwAn[LKRuleCreationException]
      NegRightRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D ), C ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val p = NegRightRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D ), A )

      if ( p.mainIndices.length != 1 )
        failure

      val i = p.mainIndices.head

      p.endSequent( i ) must beEqualTo( Neg( A ) )
    }

    "correctly return its aux formulas" in {
      val p = NegRightRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D :+ E ), A )

      if ( p.auxIndices.length != 1 )
        failure
      if ( p.auxIndices.head.length != 1 )
        failure

      for ( i <- p.auxIndices.head ) {
        p.premise( i ) must beEqualTo( A )
      }
      success
    }

    "correctly connect occurrences" in {
      // end sequent of p: A, C :- D, E, ¬B
      val p = NegRightRule( ArbitraryAxiom( A +: B +: C +: Sequent() :+ D :+ E ), B )

      val o = p.getOccConnector

      testChildren( o, "¬:r" )(
        p.premise,
        Seq( Ant( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Ant( 1 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 1 ) )
      )

      testParents( o, "¬:r" )(
        p.endSequent,
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 1 ) ),
        Seq( Ant( 1 ) )
      )
    }
  }

  "AndLeftRule" should {

    "correctly create a proof" in {
      AndLeftRule( WeakeningLeftRule( LogicalAxiom( A ), B ), Ant( 0 ), Ant( 1 ) )
      AndLeftRule( WeakeningLeftRule( LogicalAxiom( A ), B ), A, B )
      AndLeftRule( WeakeningLeftRule( LogicalAxiom( A ), B ), And( A, B ) )

      success
    }

    "refuse to construct a proof" in {
      AndLeftRule( LogicalAxiom( A ), Ant( 0 ), Ant( 1 ) ) must throwAn[LKRuleCreationException]
      AndLeftRule( LogicalAxiom( A ), Ant( 0 ), Ant( 0 ) ) must throwAn[LKRuleCreationException]
      AndLeftRule( LogicalAxiom( B ), A ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val p = AndLeftRule( WeakeningLeftRule( LogicalAxiom( A ), B ), A, B )

      if ( p.mainIndices.length != 1 )
        failure

      val i = p.mainIndices.head

      p.endSequent( i ) must beEqualTo( And( A, B ) )
    }

    "correctly return its aux formulas" in {
      val p = AndLeftRule( WeakeningLeftRule( LogicalAxiom( A ), B ), A, B )

      if ( p.auxIndices.length != 1 )
        failure
      if ( p.auxIndices.head.length != 2 )
        failure

      p.premise( p.auxIndices.head.head ) must beEqualTo( A )
      p.premise( p.auxIndices.head.tail.head ) must beEqualTo( B )
      success
    }

    "correctly connect occurrences" in {
      // end sequent of p: A∧A, B, C :- A, B
      val p = AndLeftRule( ArbitraryAxiom( B +: A +: C +: A +: Sequent() :+ A :+ B ), A, A )

      val o = p.getOccConnector

      testParents( o, "∧_l" )(
        p.endSequent,
        Seq( Ant( 1 ), Ant( 3 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),
        Seq( Suc( 0 ) ),
        Seq( Suc( 1 ) )
      )

      testChildren( o, "∧_l" )(
        p.premise,
        Seq( Ant( 1 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),
        Seq( Ant( 0 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 1 ) )
      )
    }
  }

  "AndRightRule" should {

    "correctly construct a proof" in {
      AndRightRule( ArbitraryAxiom( A +: Sequent() :+ C ), Suc( 0 ), ArbitraryAxiom( B +: Sequent() :+ D ), Suc( 0 ) )
      AndRightRule( ArbitraryAxiom( A +: Sequent() :+ C ), C, ArbitraryAxiom( B +: Sequent() :+ D ), D )
      AndRightRule( ArbitraryAxiom( A +: Sequent() :+ C ), ArbitraryAxiom( B +: Sequent() :+ D ), And( C, D ) )
      success
    }

    "refuse to construct a proof" in {
      AndRightRule( ArbitraryAxiom( A +: Sequent() :+ C ), Ant( 0 ), ArbitraryAxiom( B +: Sequent() :+ D ), Suc( 0 ) ) must throwAn[LKRuleCreationException]
      AndRightRule( ArbitraryAxiom( A +: Sequent() :+ C ), Suc( 0 ), ArbitraryAxiom( B +: Sequent() :+ D ), Ant( 0 ) ) must throwAn[LKRuleCreationException]
      AndRightRule( ArbitraryAxiom( A +: Sequent() :+ C ), Suc( 2 ), ArbitraryAxiom( B +: Sequent() :+ D ), Suc( 0 ) ) must throwAn[LKRuleCreationException]
      AndRightRule( ArbitraryAxiom( A +: Sequent() :+ C ), Suc( 0 ), ArbitraryAxiom( B +: Sequent() :+ D ), Suc( 2 ) ) must throwAn[LKRuleCreationException]
      AndRightRule( ArbitraryAxiom( A +: Sequent() :+ C ), B, ArbitraryAxiom( B +: Sequent() :+ D ), D ) must throwAn[LKRuleCreationException]
      AndRightRule( ArbitraryAxiom( A +: Sequent() :+ C ), C, ArbitraryAxiom( B +: Sequent() :+ D ), C ) must throwAn[LKRuleCreationException]
      AndRightRule( ArbitraryAxiom( A +: Sequent() :+ C ), ArbitraryAxiom( B +: Sequent() :+ D ), Or( C, D ) ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val p = AndRightRule( ArbitraryAxiom( A +: Sequent() :+ C ), Suc( 0 ), ArbitraryAxiom( B +: Sequent() :+ D ), Suc( 0 ) )

      if ( p.mainIndices.length != 1 )
        failure

      p.endSequent( p.mainIndices.head ) must beEqualTo( And( C, D ) )
    }

    "correctly return its aux formulas" in {
      val p = AndRightRule( ArbitraryAxiom( A +: Sequent() :+ C ), Suc( 0 ), ArbitraryAxiom( B +: Sequent() :+ D ), Suc( 0 ) )

      if ( p.auxIndices.length != 2 )
        failure

      if ( p.auxIndices.head.length != 1 )
        failure

      if ( p.auxIndices.tail.head.length != 1 )
        failure

      p.leftPremise( p.auxIndices.head.head ) must beEqualTo( C )
      p.rightPremise( p.auxIndices.tail.head.head ) must beEqualTo( D )
      success
    }

    "correctly connect occurrences" in {
      val ax1 = ArbitraryAxiom( A +: Sequent() :+ B :+ C :+ D )
      val ax2 = ArbitraryAxiom( A +: Sequent() :+ B :+ E :+ F )

      // end sequent of p: A, A :- B, D, B, F, C∧E
      val p = AndRightRule( ax1, ax2, And( C, E ) )

      val oL = p.getLeftOccConnector
      val oR = p.getRightOccConnector

      testChildren( oL, "∧:r" )(
        p.leftPremise,
        Seq( Ant( 0 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 4 ) ),
        Seq( Suc( 1 ) )
      )

      testParents( oL, "∧:r" )(
        p.endSequent,
        Seq( Ant( 0 ) ),
        Seq(),

        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq(),
        Seq(),
        Seq( Suc( 1 ) )
      )

      testChildren( oR, "∧:r" )(
        p.rightPremise,
        Seq( Ant( 1 ) ),

        Seq( Suc( 2 ) ),
        Seq( Suc( 4 ) ),
        Seq( Suc( 3 ) )
      )

      testParents( oR, "∧:r" )(
        p.endSequent,
        Seq(),
        Seq( Ant( 0 ) ),

        Seq(),
        Seq(),
        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Suc( 1 ) )
      )
    }
  }

  "OrLeftRule" should {

    "correctly construct a proof" in {
      OrLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), Ant( 0 ), ArbitraryAxiom( B +: Sequent() :+ D ), Ant( 0 ) )
      OrLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), A, ArbitraryAxiom( B +: Sequent() :+ D ), B )
      OrLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), ArbitraryAxiom( B +: Sequent() :+ D ), Or( A, B ) )
      success
    }

    "refuse to construct a proof" in {
      OrLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), Suc( 0 ), ArbitraryAxiom( B +: Sequent() :+ D ), Ant( 0 ) ) must throwAn[LKRuleCreationException]
      OrLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), Ant( 0 ), ArbitraryAxiom( B +: Sequent() :+ D ), Suc( 0 ) ) must throwAn[LKRuleCreationException]
      OrLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), Ant( 2 ), ArbitraryAxiom( B +: Sequent() :+ D ), Ant( 0 ) ) must throwAn[LKRuleCreationException]
      OrLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), Ant( 0 ), ArbitraryAxiom( B +: Sequent() :+ D ), Ant( 2 ) ) must throwAn[LKRuleCreationException]
      OrLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), B, ArbitraryAxiom( B +: Sequent() :+ D ), B ) must throwAn[LKRuleCreationException]
      OrLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), A, ArbitraryAxiom( B +: Sequent() :+ D ), D ) must throwAn[LKRuleCreationException]
      OrLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), ArbitraryAxiom( B +: Sequent() :+ D ), And( A, B ) ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val p = OrLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), Ant( 0 ), ArbitraryAxiom( B +: Sequent() :+ D ), Ant( 0 ) )

      if ( p.mainIndices.length != 1 )
        failure

      p.endSequent( p.mainIndices.head ) must beEqualTo( Or( A, B ) )
    }

    "correctly return its aux formulas" in {
      val p = OrLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), Ant( 0 ), ArbitraryAxiom( B +: Sequent() :+ D ), Ant( 0 ) )

      if ( p.auxIndices.length != 2 )
        failure

      if ( p.auxIndices.head.length != 1 )
        failure

      if ( p.auxIndices.tail.head.length != 1 )
        failure

      p.leftPremise( p.auxIndices.head.head ) must beEqualTo( A )
      p.rightPremise( p.auxIndices.tail.head.head ) must beEqualTo( B )
      success
    }

    "correctly connect occurrences" in {
      val ax1 = ArbitraryAxiom( A +: B +: C +: Sequent() :+ D )
      val ax2 = ArbitraryAxiom( A +: E +: F +: Sequent() :+ C )

      // end sequent of p: B∨E, A, C, A, F :- D, C
      val p = OrLeftRule( ax1, ax2, Or( B, E ) )

      val oL = p.getLeftOccConnector
      val oR = p.getRightOccConnector

      testChildren( oL, "∨:l" )(
        p.leftPremise,
        Seq( Ant( 1 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),

        Seq( Suc( 0 ) )
      )

      testParents( oL, "∨:l" )(
        p.endSequent,
        Seq( Ant( 1 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),
        Seq(),
        Seq(),

        Seq( Suc( 0 ) ),
        Seq()
      )

      testChildren( oR, "∨:l" )(
        p.rightPremise,
        Seq( Ant( 3 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 4 ) ),

        Seq( Suc( 1 ) )
      )

      testParents( oR, "∨:l" )(
        p.endSequent,
        Seq( Ant( 1 ) ),
        Seq(),
        Seq(),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),

        Seq(),
        Seq( Suc( 0 ) )
      )
    }
  }

  "OrRightRule" should {

    "correctly create a proof" in {
      OrRightRule( WeakeningRightRule( LogicalAxiom( A ), B ), Suc( 0 ), Suc( 1 ) )
      OrRightRule( WeakeningRightRule( LogicalAxiom( A ), B ), A, B )
      OrRightRule( WeakeningRightRule( LogicalAxiom( A ), B ), Or( A, B ) )

      success
    }

    "refuse to construct a proof" in {
      OrRightRule( LogicalAxiom( A ), Suc( 0 ), Suc( 1 ) ) must throwAn[LKRuleCreationException]
      OrRightRule( LogicalAxiom( A ), Suc( 0 ), Suc( 0 ) ) must throwAn[LKRuleCreationException]
      OrRightRule( LogicalAxiom( B ), A ) must throwAn[LKRuleCreationException]
      OrRightRule( LogicalAxiom( A ), Or( A, B ) ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val p = OrRightRule( WeakeningRightRule( LogicalAxiom( A ), B ), A, B )

      if ( p.mainIndices.length != 1 )
        failure

      val i = p.mainIndices.head

      p.endSequent( i ) must beEqualTo( Or( A, B ) )
    }

    "correctly return its aux formulas" in {
      val p = OrRightRule( WeakeningRightRule( LogicalAxiom( A ), B ), A, B )

      if ( p.auxIndices.length != 1 )
        failure
      if ( p.auxIndices.head.length != 2 )
        failure

      p.premise( p.auxIndices.head.head ) must beEqualTo( A )
      p.premise( p.auxIndices.head.tail.head ) must beEqualTo( B )
      success
    }

    "correctly connect occurrences" in {
      // end sequent of p: A :- B, D, B, C∨E
      val p = OrRightRule( ArbitraryAxiom( A +: Sequent() :+ B :+ C :+ D :+ E :+ B ), Or( C, E ) )

      val o = p.getOccConnector

      testParents( o, "∨:r" )(
        p.endSequent,
        Seq( Ant( 0 ) ),
        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Suc( 4 ) ),
        Seq( Suc( 1 ), Suc( 3 ) )
      )

      testChildren( o, "∨:r" )(
        p.premise,
        Seq( Ant( 0 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 3 ) ),
        Seq( Suc( 1 ) ),
        Seq( Suc( 3 ) ),
        Seq( Suc( 2 ) )
      )
    }
  }

  "ImpLeftRule" should {

    "correctly construct a proof" in {
      ImpLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), Suc( 0 ), ArbitraryAxiom( B +: Sequent() :+ D ), Ant( 0 ) )
      ImpLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), C, ArbitraryAxiom( B +: Sequent() :+ D ), B )
      ImpLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), ArbitraryAxiom( B +: Sequent() :+ D ), Imp( C, B ) )
      success
    }

    "refuse to construct a proof" in {
      ImpLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), Ant( 0 ), ArbitraryAxiom( B +: Sequent() :+ D ), Ant( 0 ) ) must throwAn[LKRuleCreationException]
      ImpLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), Suc( 0 ), ArbitraryAxiom( B +: Sequent() :+ D ), Suc( 0 ) ) must throwAn[LKRuleCreationException]
      ImpLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), Suc( 2 ), ArbitraryAxiom( B +: Sequent() :+ D ), Ant( 0 ) ) must throwAn[LKRuleCreationException]
      ImpLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), Suc( 0 ), ArbitraryAxiom( B +: Sequent() :+ D ), Ant( 2 ) ) must throwAn[LKRuleCreationException]
      ImpLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), B, ArbitraryAxiom( B +: Sequent() :+ D ), B ) must throwAn[LKRuleCreationException]
      ImpLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), C, ArbitraryAxiom( B +: Sequent() :+ D ), D ) must throwAn[LKRuleCreationException]
      ImpLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), ArbitraryAxiom( B +: Sequent() :+ D ), And( A, B ) ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val p = ImpLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), Suc( 0 ), ArbitraryAxiom( B +: Sequent() :+ D ), Ant( 0 ) )

      if ( p.mainIndices.length != 1 )
        failure

      p.endSequent( p.mainIndices.head ) must beEqualTo( Imp( C, B ) )
    }

    "correctly return its aux formulas" in {
      val p = ImpLeftRule( ArbitraryAxiom( A +: Sequent() :+ C ), Suc( 0 ), ArbitraryAxiom( B +: Sequent() :+ D ), Ant( 0 ) )

      if ( p.auxIndices.length != 2 )
        failure

      if ( p.auxIndices.head.length != 1 )
        failure

      if ( p.auxIndices.tail.head.length != 1 )
        failure

      p.leftPremise( p.auxIndices.head.head ) must beEqualTo( C )
      p.rightPremise( p.auxIndices.tail.head.head ) must beEqualTo( B )
      success
    }

    "correctly connect occurrences" in {
      val ax1 = ArbitraryAxiom( A +: Sequent() :+ B :+ C :+ D )
      val ax2 = ArbitraryAxiom( A +: E +: F +: Sequent() :+ C )

      // end sequent of p: C -> E, A, A, F :- B, D, C
      val p = ImpLeftRule( ax1, ax2, Imp( C, E ) )

      val oL = p.getLeftOccConnector
      val oR = p.getRightOccConnector

      testChildren( oL, "→:l" )(
        p.leftPremise,
        Seq( Ant( 1 ) ),

        Seq( Suc( 0 ) ),
        Seq( Ant( 0 ) ),
        Seq( Suc( 1 ) )
      )

      testParents( oL, "→:l" )(
        p.endSequent,
        Seq( Suc( 1 ) ),
        Seq( Ant( 0 ) ),
        Seq(),
        Seq(),

        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq()
      )

      testChildren( oR, "→:l" )(
        p.rightPremise,
        Seq( Ant( 2 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 3 ) ),

        Seq( Suc( 2 ) )
      )

      testParents( oR, "→:l" )(
        p.endSequent,
        Seq( Ant( 1 ) ),
        Seq(),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),

        Seq(),
        Seq(),
        Seq( Suc( 0 ) )
      )
    }
  }

  "ImpRightRule" should {

    "correctly create a proof" in {
      ImpRightRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D ), Ant( 0 ), Suc( 1 ) )
      ImpRightRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D ), B, D )
      ImpRightRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D ), Imp( A, C ) )

      success
    }

    "refuse to construct a proof" in {
      ImpRightRule( LogicalAxiom( A ), Suc( 0 ), Suc( 1 ) ) must throwAn[LKRuleCreationException]
      ImpRightRule( LogicalAxiom( A ), Ant( 0 ), Ant( 0 ) ) must throwAn[LKRuleCreationException]
      ImpRightRule( LogicalAxiom( B ), A, B ) must throwAn[LKRuleCreationException]
      ImpRightRule( LogicalAxiom( A ), Imp( A, B ) ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val p = ImpRightRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D ), A, D )

      if ( p.mainIndices.length != 1 )
        failure

      val i = p.mainIndices.head

      p.endSequent( i ) must beEqualTo( Imp( A, D ) )
    }

    "correctly return its aux formulas" in {
      val p = ImpRightRule( ArbitraryAxiom( A +: B +: Sequent() :+ C :+ D ), A, D )

      if ( p.auxIndices.length != 1 )
        failure
      if ( p.auxIndices.head.length != 2 )
        failure

      p.premise( p.auxIndices.head.head ) must beEqualTo( A )
      p.premise( p.auxIndices.head.tail.head ) must beEqualTo( D )
      success
    }

    "correctly connect occurrences" in {
      // end sequent of p: A, C :- D, F, B→E
      val p = ImpRightRule( ArbitraryAxiom( A +: B +: C +: Sequent() :+ D :+ E :+ F ), Imp( B, E ) )

      val o = p.getOccConnector

      testParents( o, "→:r" )(
        p.endSequent,
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Ant( 1 ), Suc( 1 ) )
      )

      testChildren( o, "→:r" )(
        p.premise,
        Seq( Ant( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Ant( 1 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Suc( 1 ) )
      )
    }
  }

  "ForallRightRule" should {
    "correctly construct a proof" in {
      val ax = ArbitraryAxiom( Sequent() :+ P( alpha ) :+ P( x ) )
      ForallRightRule( ax, Suc( 0 ), alpha, x )
      ForallRightRule( ax, All( x, P( x ) ), alpha )
      ForallRightRule( ax, All( x, P( x ) ) )

      success
    }

    "refuse to construct a proof" in {
      val ax = ArbitraryAxiom( P( alpha ) +: Sequent() :+ P( alpha ) :+ P( x ) )

      ForallRightRule( ax, Ant( 0 ), alpha, x ) must throwAn[LKRuleCreationException]
      ForallRightRule( ax, Suc( 2 ), alpha, x ) must throwAn[LKRuleCreationException]
      ForallRightRule( ax, Suc( 0 ), alpha, x ) must throwAn[LKRuleCreationException]
      ForallRightRule( ax, P( x ), alpha ) must throwAn[LKRuleCreationException]
      ForallRightRule( ax, All( x, P( x ) ), y ) must throwAn[LKRuleCreationException]
      ForallRightRule( ax, All( y, P( y ) ) ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val ax = ArbitraryAxiom( Sequent() :+ P( alpha ) :+ P( x ) )

      val p = ForallRightRule( ax, Suc( 0 ), alpha, x )

      if ( p.mainIndices.length != 1 )
        failure

      p.mainFormulas.head must beEqualTo( All( x, P( x ) ) )
    }

    "correctly return its aux formula" in {
      val ax = ArbitraryAxiom( Sequent() :+ P( alpha ) :+ P( x ) )

      val p = ForallRightRule( ax, Suc( 0 ), alpha, x )

      if ( p.auxIndices.length != 1 )
        failure

      if ( p.auxIndices.head.length != 1 )
        failure

      p.auxFormulas.head.head must beEqualTo( P( alpha ) )
    }

    "correctly connect occurrences" in {
      val ax = ArbitraryAxiom( A +: Sequent() :+ B :+ P( alpha ) :+ C )

      // end sequent of p: A :- B, C, ∀x.P
      val p = ForallRightRule( ax, All( x, P( x ) ), alpha )

      val o = p.getOccConnector

      testChildren( o, "∀:r" )(
        p.premise,
        Seq( Ant( 0 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Suc( 1 ) )
      )

      testParents( o, "∀:r" )(
        p.endSequent,
        Seq( Ant( 0 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Suc( 1 ) )
      )
    }
  }

  "ExistsLeftRule" should {
    "correctly construct a proof" in {
      val ax = ArbitraryAxiom( P( alpha ) +: P( x ) +: Sequent() )
      ExistsLeftRule( ax, Ant( 0 ), alpha, x )
      ExistsLeftRule( ax, Ex( x, P( x ) ), alpha )
      ExistsLeftRule( ax, Ex( x, P( x ) ) )

      success
    }

    "refuse to construct a proof" in {
      val ax = ArbitraryAxiom( P( alpha ) +: P( x ) +: Sequent() :+ P( alpha ) )

      ExistsLeftRule( ax, Suc( 0 ), alpha, x ) must throwAn[LKRuleCreationException]
      ExistsLeftRule( ax, Ant( 2 ), alpha, x ) must throwAn[LKRuleCreationException]
      ExistsLeftRule( ax, Suc( 0 ), alpha, x ) must throwAn[LKRuleCreationException]
      ExistsLeftRule( ax, P( x ), alpha ) must throwAn[LKRuleCreationException]
      ExistsLeftRule( ax, Ex( x, P( x ) ), y ) must throwAn[LKRuleCreationException]
      ExistsLeftRule( ax, Ex( y, P( y ) ) ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val ax = ArbitraryAxiom( P( alpha ) +: P( x ) +: Sequent() )

      val p = ExistsLeftRule( ax, Ant( 0 ), alpha, x )

      if ( p.mainIndices.length != 1 )
        failure

      p.mainFormulas.head must beEqualTo( Ex( x, P( x ) ) )
    }

    "correctly return its aux formula" in {
      val ax = ArbitraryAxiom( P( alpha ) +: P( x ) +: Sequent() )

      val p = ExistsLeftRule( ax, Ant( 0 ), alpha, x )

      if ( p.auxIndices.length != 1 )
        failure

      if ( p.auxIndices.head.length != 1 )
        failure

      p.auxFormulas.head.head must beEqualTo( P( alpha ) )
    }

    "correctly connect occurrences" in {
      val ax = ArbitraryAxiom( A +: P( alpha ) +: B +: Sequent() :+ C )

      // end sequent of p: ∀x.P, A, B :- C
      val p = ExistsLeftRule( ax, Ex( x, P( x ) ), alpha )

      val o = p.getOccConnector

      testChildren( o, "∃:l" )(
        p.premise,
        Seq( Ant( 1 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),

        Seq( Suc( 0 ) )
      )

      testParents( o, "∃:l" )(
        p.endSequent,
        Seq( Ant( 1 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),

        Seq( Suc( 0 ) )
      )
    }
  }

  "EqualityLeft1Rule" should {
    "correctly construct a proof" in {
      val ax = Axiom( Eq( c, d ) +: Pc +: Sequent() )

      EqualityLeft1Rule( ax, Ant( 0 ), Ant( 1 ), HOLPosition( 2 ) )
      EqualityLeft1Rule( ax, Eq( c, d ), Pc, Pd )

      success
    }

    "refuse to construct a proof" in {
      val ax = Axiom( Eq( c, d ) +: Pd +: A +: Sequent() )

      EqualityLeft1Rule( ax, Ant( 0 ), Ant( 1 ), HOLPosition( 2 ) ) must throwAn[LKRuleCreationException]
      EqualityLeft1Rule( ax, Suc( 0 ), Ant( 1 ), HOLPosition( 2 ) ) must throwAn[LKRuleCreationException]
      EqualityLeft1Rule( ax, Ant( 0 ), Suc( 1 ), HOLPosition( 2 ) ) must throwAn[LKRuleCreationException]
      EqualityLeft1Rule( ax, Ant( 3 ), Ant( 1 ), HOLPosition( 2 ) ) must throwAn[LKRuleCreationException]
      EqualityLeft1Rule( ax, Ant( 0 ), Ant( 3 ), HOLPosition( 2 ) ) must throwAn[LKRuleCreationException]
      EqualityLeft1Rule( ax, Ant( 2 ), Ant( 1 ), HOLPosition( 2 ) ) must throwAn[LKRuleCreationException]
      EqualityLeft1Rule( ax, Suc( 0 ), Ant( 1 ), HOLPosition( 1 ) ) must throwAn[LKRuleCreationException]

      EqualityLeft1Rule( ax, Eq( c, d ), Pd, Pc ) must throwAn[LKRuleCreationException]
      EqualityLeft1Rule( ax, Eq( d, c ), Pd, Pc ) must throwAn[LKRuleCreationException]
      EqualityLeft1Rule( ax, Eq( c, d ), Pc, Pd ) must throwAn[LKRuleCreationException]
      EqualityLeft1Rule( ax, A, Pd, Pc ) must throwAn[LKRuleCreationException]
      EqualityLeft1Rule( ax, Eq( c, d ), Pd, Pd ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val ax = Axiom( Eq( c, d ) +: Pc +: Sequent() )

      val p = EqualityLeft1Rule( ax, Eq( c, d ), Pc, Pd )

      if ( p.mainIndices.length != 1 )
        failure

      p.mainFormulas.head must beEqualTo( Pd )
    }

    "correctly return its aux formulas" in {
      val ax = Axiom( Eq( c, d ) +: Pc +: Sequent() )

      val p = EqualityLeft1Rule( ax, Eq( c, d ), Pc, Pd )

      if ( p.auxIndices.length != 1 )
        failure

      if ( p.auxIndices.head.length != 2 )
        failure

      p.auxFormulas.head.head must beEqualTo( Eq( c, d ) )
      p.auxFormulas.head.tail.head must beEqualTo( Pc )
    }

    "correctly connect occurrences" in {
      val ax = Axiom( A +: Eq( c, d ) +: B +: Pc +: C +: Sequent() :+ D )

      // end sequent of p: P(d), A, c = d, B, C :- D
      val p = EqualityLeft1Rule( ax, Eq( c, d ), Pc, Pd )

      val o = p.getOccConnector

      testChildren( o, "eq:l1" )(
        p.premise,
        Seq( Ant( 1 ) ),
        Seq( Ant( 2 ) ),
        Seq( Ant( 3 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 4 ) ),

        Seq( Suc( 0 ) )
      )

      testParents( o, "eq:l1" )(
        p.endSequent,
        Seq( Ant( 3 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 1 ) ),
        Seq( Ant( 2 ) ),
        Seq( Ant( 4 ) ),

        Seq( Suc( 0 ) )
      )
    }
  }
}
