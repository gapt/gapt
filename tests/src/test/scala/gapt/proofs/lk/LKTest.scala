package gapt.proofs.lk

import gapt.expr._
import gapt.expr.hol.HOLPosition
import gapt.proofs._
import org.specs2.execute.Success
import org.specs2.mutable._

class LKTest extends Specification {
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

  def proofOf( sequent: HOLSequent ): LKProof =
    ProofLink( FOLAtom( "sorry" ), sequent )

  private def testParents( o: SequentConnector, ruleName: String )( sequent: HOLSequent, parents: Seq[SequentIndex]* ): Success = {
    val ( m, n ) = sequent.sizes
    for ( ( i, ps ) <- sequent.indices zip parents ) {
      o.parents( i ) aka s"$ruleName: Parents of $i in $sequent should be $ps" must beEqualTo( ps )
    }
    o.parents( Ant( m ) ) aka s"Parents of ${Ant( m )} in $sequent" must throwAn[IndexOutOfBoundsException]
    o.parents( Suc( n ) ) aka s"Parents of ${Suc( n )} in $sequent" must throwAn[IndexOutOfBoundsException]
    success
  }

  private def testChildren( o: SequentConnector, ruleName: String )( sequent: HOLSequent, children: Seq[SequentIndex]* ): Success = {
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

      val o = p.getSequentConnector

      testChildren( o, "w_l" )(
        p.premise,
        Seq( Ant( 1 ) ),

        Seq( Suc( 0 ) ) )

      testParents( o, "w_l" )(
        p.endSequent,
        Seq(),
        Seq( Ant( 0 ) ),
        Seq( Suc( 0 ) ) )
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

      val o = p.getSequentConnector

      testChildren( o, "w_r" )(
        p.endSequent,
        Seq( Ant( 0 ) ),
        Seq( Suc( 0 ) ) )

      testParents( o, "w_r" )(
        p.endSequent,
        Seq( Ant( 0 ) ),
        Seq( Suc( 0 ) ),
        Seq() )
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
      val p = ContractionLeftRule( proofOf( B +: A +: C +: A +: Sequent() :+ A :+ B ), A )

      val o = p.getSequentConnector

      testParents( o, "c_l" )(
        p.endSequent,
        Seq( Ant( 1 ), Ant( 3 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),
        Seq( Suc( 0 ) ),
        Seq( Suc( 1 ) ) )

      testChildren( o, "c_l" )(
        p.premise,
        Seq( Ant( 1 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),
        Seq( Ant( 0 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 1 ) ) )
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
      val p = ContractionRightRule( proofOf( A +: B +: Sequent() :+ A :+ B :+ A :+ C ), Suc( 0 ), Suc( 2 ) )

      val o = p.getSequentConnector

      testParents( o, "c_r" )(
        p.endSequent,
        Seq( Ant( 0 ) ),
        Seq( Ant( 1 ) ),

        Seq( Suc( 1 ) ),
        Seq( Suc( 3 ) ),
        Seq( Suc( 0 ), Suc( 2 ) ) )

      testChildren( o, "c_r" )(
        p.premise,
        Seq( Ant( 0 ) ),
        Seq( Ant( 1 ) ),

        Seq( Suc( 2 ) ),
        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Suc( 1 ) ) )
    }
  }

  "CutRule" should {
    "correctly produce a proof" in {
      CutRule( proofOf( A +: B +: Sequent() :+ B ), Suc( 0 ), LogicalAxiom( B ), Ant( 0 ) )
      CutRule( proofOf( A +: B +: Sequent() :+ B ), LogicalAxiom( B ), B )

      success
    }

    "refuse to produce a proof" in {
      val p1 = proofOf( Sequent() :+ A :+ B )
      val p2 = proofOf( C +: B +: Sequent() )

      CutRule( p1, Ant( 0 ), p2, Ant( 0 ) ) must throwAn[LKRuleCreationException]
      CutRule( p1, Suc( 0 ), p2, Suc( 0 ) ) must throwAn[LKRuleCreationException]
      CutRule( p1, Suc( 0 ), p2, Ant( 0 ) ) must throwAn[LKRuleCreationException]
      CutRule( p1, Suc( 2 ), p2, Ant( 0 ) ) must throwAn[LKRuleCreationException]
      CutRule( p1, Suc( 0 ), p2, Ant( 3 ) ) must throwAn[LKRuleCreationException]
    }

    "correctly return its aux formulas" in {
      val p1 = proofOf( Sequent() :+ A :+ B )
      val p2 = proofOf( C +: B +: Sequent() )

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
      val p1 = proofOf( A +: B +: Sequent() :+ A :+ B :+ C )
      val p2 = proofOf( D +: B +: E +: F +: Sequent() :+ B :+ E )

      // end sequent of p: A, B, D, E, F :- A, C, B, E
      val p = CutRule( p1, p2, B )
      val oL = p.getLeftSequentConnector
      val oR = p.getRightSequentConnector

      testChildren( oL, "cut" )(
        p.leftPremise,
        Seq( Ant( 0 ) ),
        Seq( Ant( 1 ) ),

        Seq( Suc( 0 ) ),
        Seq(),
        Seq( Suc( 1 ) ) )

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
        Seq() )

      testChildren( oR, "cut" )(
        p.rightPremise,
        Seq( Ant( 2 ) ),
        Seq(),
        Seq( Ant( 3 ) ),
        Seq( Ant( 4 ) ),

        Seq( Suc( 2 ) ),
        Seq( Suc( 3 ) ) )

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
        Seq( Suc( 1 ) ) )
    }
  }

  "NegLeftRule" should {

    "correctly create a proof" in {
      NegLeftRule( proofOf( A +: B +: Sequent() :+ C :+ D ), Suc( 0 ) )
      NegLeftRule( proofOf( A +: B +: Sequent() :+ C :+ D ), C )

      success
    }

    "refuse to create a proof" in {
      NegLeftRule( proofOf( A +: B +: Sequent() :+ C :+ D ), Ant( 0 ) ) must throwAn[LKRuleCreationException]
      NegLeftRule( proofOf( A +: B +: Sequent() :+ C :+ D ), Suc( 2 ) ) must throwAn[LKRuleCreationException]
      NegLeftRule( proofOf( A +: B +: Sequent() :+ C :+ D ), A ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val p = NegLeftRule( proofOf( A +: B +: Sequent() :+ C :+ D ), C )

      if ( p.mainIndices.length != 1 )
        failure

      val i = p.mainIndices.head

      p.endSequent( i ) must beEqualTo( Neg( C ) )
    }

    "correctly return its aux formulas" in {
      val p = NegLeftRule( proofOf( A +: B +: Sequent() :+ C :+ D :+ E ), C )

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
      val p = NegLeftRule( proofOf( A +: B +: Sequent() :+ C :+ D :+ E ), D )

      val o = p.getSequentConnector

      testChildren( o, "¬:l" )(
        p.premise,
        Seq( Ant( 1 ) ),
        Seq( Ant( 2 ) ),

        Seq( Suc( 0 ) ),
        Seq( Ant( 0 ) ),
        Seq( Suc( 1 ) ) )

      testParents( o, "¬:l" )(
        p.endSequent,
        Seq( Suc( 1 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 1 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ) )
    }
  }

  "NegRightRule" should {

    "correctly create a proof" in {
      NegRightRule( proofOf( A +: B +: Sequent() :+ C :+ D ), Ant( 0 ) )
      NegRightRule( proofOf( A +: B +: Sequent() :+ C :+ D ), A )

      success
    }

    "refuse to create a proof" in {
      NegRightRule( proofOf( A +: B +: Sequent() :+ C :+ D ), Suc( 0 ) ) must throwAn[LKRuleCreationException]
      NegRightRule( proofOf( A +: B +: Sequent() :+ C :+ D ), Ant( 2 ) ) must throwAn[LKRuleCreationException]
      NegRightRule( proofOf( A +: B +: Sequent() :+ C :+ D ), C ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val p = NegRightRule( proofOf( A +: B +: Sequent() :+ C :+ D ), A )

      if ( p.mainIndices.length != 1 )
        failure

      val i = p.mainIndices.head

      p.endSequent( i ) must beEqualTo( Neg( A ) )
    }

    "correctly return its aux formulas" in {
      val p = NegRightRule( proofOf( A +: B +: Sequent() :+ C :+ D :+ E ), A )

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
      val p = NegRightRule( proofOf( A +: B +: C +: Sequent() :+ D :+ E ), B )

      val o = p.getSequentConnector

      testChildren( o, "¬:r" )(
        p.premise,
        Seq( Ant( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Ant( 1 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 1 ) ) )

      testParents( o, "¬:r" )(
        p.endSequent,
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 1 ) ),
        Seq( Ant( 1 ) ) )
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
      val p = AndLeftRule( proofOf( B +: A +: C +: A +: Sequent() :+ A :+ B ), A, A )

      val o = p.getSequentConnector

      testParents( o, "∧_l" )(
        p.endSequent,
        Seq( Ant( 1 ), Ant( 3 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),
        Seq( Suc( 0 ) ),
        Seq( Suc( 1 ) ) )

      testChildren( o, "∧_l" )(
        p.premise,
        Seq( Ant( 1 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),
        Seq( Ant( 0 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 1 ) ) )
    }
  }

  "AndRightRule" should {

    "correctly construct a proof" in {
      AndRightRule( proofOf( A +: Sequent() :+ C ), Suc( 0 ), proofOf( B +: Sequent() :+ D ), Suc( 0 ) )
      AndRightRule( proofOf( A +: Sequent() :+ C ), C, proofOf( B +: Sequent() :+ D ), D )
      AndRightRule( proofOf( A +: Sequent() :+ C ), proofOf( B +: Sequent() :+ D ), And( C, D ) )
      success
    }

    "refuse to construct a proof" in {
      AndRightRule( proofOf( A +: Sequent() :+ C ), Ant( 0 ), proofOf( B +: Sequent() :+ D ), Suc( 0 ) ) must throwAn[LKRuleCreationException]
      AndRightRule( proofOf( A +: Sequent() :+ C ), Suc( 0 ), proofOf( B +: Sequent() :+ D ), Ant( 0 ) ) must throwAn[LKRuleCreationException]
      AndRightRule( proofOf( A +: Sequent() :+ C ), Suc( 2 ), proofOf( B +: Sequent() :+ D ), Suc( 0 ) ) must throwAn[LKRuleCreationException]
      AndRightRule( proofOf( A +: Sequent() :+ C ), Suc( 0 ), proofOf( B +: Sequent() :+ D ), Suc( 2 ) ) must throwAn[LKRuleCreationException]
      AndRightRule( proofOf( A +: Sequent() :+ C ), B, proofOf( B +: Sequent() :+ D ), D ) must throwAn[LKRuleCreationException]
      AndRightRule( proofOf( A +: Sequent() :+ C ), C, proofOf( B +: Sequent() :+ D ), C ) must throwAn[LKRuleCreationException]
      AndRightRule( proofOf( A +: Sequent() :+ C ), proofOf( B +: Sequent() :+ D ), Or( C, D ) ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val p = AndRightRule( proofOf( A +: Sequent() :+ C ), Suc( 0 ), proofOf( B +: Sequent() :+ D ), Suc( 0 ) )

      if ( p.mainIndices.length != 1 )
        failure

      p.endSequent( p.mainIndices.head ) must beEqualTo( And( C, D ) )
    }

    "correctly return its aux formulas" in {
      val p = AndRightRule( proofOf( A +: Sequent() :+ C ), Suc( 0 ), proofOf( B +: Sequent() :+ D ), Suc( 0 ) )

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
      val ax1 = proofOf( A +: Sequent() :+ B :+ C :+ D )
      val ax2 = proofOf( A +: Sequent() :+ B :+ E :+ F )

      // end sequent of p: A, A :- B, D, B, F, C∧E
      val p = AndRightRule( ax1, ax2, And( C, E ) )

      val oL = p.getLeftSequentConnector
      val oR = p.getRightSequentConnector

      testChildren( oL, "∧:r" )(
        p.leftPremise,
        Seq( Ant( 0 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 4 ) ),
        Seq( Suc( 1 ) ) )

      testParents( oL, "∧:r" )(
        p.endSequent,
        Seq( Ant( 0 ) ),
        Seq(),

        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq(),
        Seq(),
        Seq( Suc( 1 ) ) )

      testChildren( oR, "∧:r" )(
        p.rightPremise,
        Seq( Ant( 1 ) ),

        Seq( Suc( 2 ) ),
        Seq( Suc( 4 ) ),
        Seq( Suc( 3 ) ) )

      testParents( oR, "∧:r" )(
        p.endSequent,
        Seq(),
        Seq( Ant( 0 ) ),

        Seq(),
        Seq(),
        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Suc( 1 ) ) )
    }
  }

  "OrLeftRule" should {

    "correctly construct a proof" in {
      OrLeftRule( proofOf( A +: Sequent() :+ C ), Ant( 0 ), proofOf( B +: Sequent() :+ D ), Ant( 0 ) )
      OrLeftRule( proofOf( A +: Sequent() :+ C ), A, proofOf( B +: Sequent() :+ D ), B )
      OrLeftRule( proofOf( A +: Sequent() :+ C ), proofOf( B +: Sequent() :+ D ), Or( A, B ) )
      success
    }

    "refuse to construct a proof" in {
      OrLeftRule( proofOf( A +: Sequent() :+ C ), Suc( 0 ), proofOf( B +: Sequent() :+ D ), Ant( 0 ) ) must throwAn[LKRuleCreationException]
      OrLeftRule( proofOf( A +: Sequent() :+ C ), Ant( 0 ), proofOf( B +: Sequent() :+ D ), Suc( 0 ) ) must throwAn[LKRuleCreationException]
      OrLeftRule( proofOf( A +: Sequent() :+ C ), Ant( 2 ), proofOf( B +: Sequent() :+ D ), Ant( 0 ) ) must throwAn[LKRuleCreationException]
      OrLeftRule( proofOf( A +: Sequent() :+ C ), Ant( 0 ), proofOf( B +: Sequent() :+ D ), Ant( 2 ) ) must throwAn[LKRuleCreationException]
      OrLeftRule( proofOf( A +: Sequent() :+ C ), B, proofOf( B +: Sequent() :+ D ), B ) must throwAn[LKRuleCreationException]
      OrLeftRule( proofOf( A +: Sequent() :+ C ), A, proofOf( B +: Sequent() :+ D ), D ) must throwAn[LKRuleCreationException]
      OrLeftRule( proofOf( A +: Sequent() :+ C ), proofOf( B +: Sequent() :+ D ), And( A, B ) ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val p = OrLeftRule( proofOf( A +: Sequent() :+ C ), Ant( 0 ), proofOf( B +: Sequent() :+ D ), Ant( 0 ) )

      if ( p.mainIndices.length != 1 )
        failure

      p.endSequent( p.mainIndices.head ) must beEqualTo( Or( A, B ) )
    }

    "correctly return its aux formulas" in {
      val p = OrLeftRule( proofOf( A +: Sequent() :+ C ), Ant( 0 ), proofOf( B +: Sequent() :+ D ), Ant( 0 ) )

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
      val ax1 = proofOf( A +: B +: C +: Sequent() :+ D )
      val ax2 = proofOf( A +: E +: F +: Sequent() :+ C )

      // end sequent of p: B∨E, A, C, A, F :- D, C
      val p = OrLeftRule( ax1, ax2, Or( B, E ) )

      val oL = p.getLeftSequentConnector
      val oR = p.getRightSequentConnector

      testChildren( oL, "∨:l" )(
        p.leftPremise,
        Seq( Ant( 1 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),

        Seq( Suc( 0 ) ) )

      testParents( oL, "∨:l" )(
        p.endSequent,
        Seq( Ant( 1 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),
        Seq(),
        Seq(),

        Seq( Suc( 0 ) ),
        Seq() )

      testChildren( oR, "∨:l" )(
        p.rightPremise,
        Seq( Ant( 3 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 4 ) ),

        Seq( Suc( 1 ) ) )

      testParents( oR, "∨:l" )(
        p.endSequent,
        Seq( Ant( 1 ) ),
        Seq(),
        Seq(),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),

        Seq(),
        Seq( Suc( 0 ) ) )
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
      val p = OrRightRule( proofOf( A +: Sequent() :+ B :+ C :+ D :+ E :+ B ), Or( C, E ) )

      val o = p.getSequentConnector

      testParents( o, "∨:r" )(
        p.endSequent,
        Seq( Ant( 0 ) ),
        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Suc( 4 ) ),
        Seq( Suc( 1 ), Suc( 3 ) ) )

      testChildren( o, "∨:r" )(
        p.premise,
        Seq( Ant( 0 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 3 ) ),
        Seq( Suc( 1 ) ),
        Seq( Suc( 3 ) ),
        Seq( Suc( 2 ) ) )
    }
  }

  "ImpLeftRule" should {

    "correctly construct a proof" in {
      ImpLeftRule( proofOf( A +: Sequent() :+ C ), Suc( 0 ), proofOf( B +: Sequent() :+ D ), Ant( 0 ) )
      ImpLeftRule( proofOf( A +: Sequent() :+ C ), C, proofOf( B +: Sequent() :+ D ), B )
      ImpLeftRule( proofOf( A +: Sequent() :+ C ), proofOf( B +: Sequent() :+ D ), Imp( C, B ) )
      success
    }

    "refuse to construct a proof" in {
      ImpLeftRule( proofOf( A +: Sequent() :+ C ), Ant( 0 ), proofOf( B +: Sequent() :+ D ), Ant( 0 ) ) must throwAn[LKRuleCreationException]
      ImpLeftRule( proofOf( A +: Sequent() :+ C ), Suc( 0 ), proofOf( B +: Sequent() :+ D ), Suc( 0 ) ) must throwAn[LKRuleCreationException]
      ImpLeftRule( proofOf( A +: Sequent() :+ C ), Suc( 2 ), proofOf( B +: Sequent() :+ D ), Ant( 0 ) ) must throwAn[LKRuleCreationException]
      ImpLeftRule( proofOf( A +: Sequent() :+ C ), Suc( 0 ), proofOf( B +: Sequent() :+ D ), Ant( 2 ) ) must throwAn[LKRuleCreationException]
      ImpLeftRule( proofOf( A +: Sequent() :+ C ), B, proofOf( B +: Sequent() :+ D ), B ) must throwAn[LKRuleCreationException]
      ImpLeftRule( proofOf( A +: Sequent() :+ C ), C, proofOf( B +: Sequent() :+ D ), D ) must throwAn[LKRuleCreationException]
      ImpLeftRule( proofOf( A +: Sequent() :+ C ), proofOf( B +: Sequent() :+ D ), And( A, B ) ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val p = ImpLeftRule( proofOf( A +: Sequent() :+ C ), Suc( 0 ), proofOf( B +: Sequent() :+ D ), Ant( 0 ) )

      if ( p.mainIndices.length != 1 )
        failure

      p.endSequent( p.mainIndices.head ) must beEqualTo( Imp( C, B ) )
    }

    "correctly return its aux formulas" in {
      val p = ImpLeftRule( proofOf( A +: Sequent() :+ C ), Suc( 0 ), proofOf( B +: Sequent() :+ D ), Ant( 0 ) )

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
      val ax1 = proofOf( A +: Sequent() :+ B :+ C :+ D )
      val ax2 = proofOf( A +: E +: F +: Sequent() :+ C )

      // end sequent of p: C -> E, A, A, F :- B, D, C
      val p = ImpLeftRule( ax1, ax2, Imp( C, E ) )

      val oL = p.getLeftSequentConnector
      val oR = p.getRightSequentConnector

      testChildren( oL, "→:l" )(
        p.leftPremise,
        Seq( Ant( 1 ) ),

        Seq( Suc( 0 ) ),
        Seq( Ant( 0 ) ),
        Seq( Suc( 1 ) ) )

      testParents( oL, "→:l" )(
        p.endSequent,
        Seq( Suc( 1 ) ),
        Seq( Ant( 0 ) ),
        Seq(),
        Seq(),

        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq() )

      testChildren( oR, "→:l" )(
        p.rightPremise,
        Seq( Ant( 2 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 3 ) ),

        Seq( Suc( 2 ) ) )

      testParents( oR, "→:l" )(
        p.endSequent,
        Seq( Ant( 1 ) ),
        Seq(),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),

        Seq(),
        Seq(),
        Seq( Suc( 0 ) ) )
    }
  }

  "ImpRightRule" should {

    "correctly create a proof" in {
      ImpRightRule( proofOf( A +: B +: Sequent() :+ C :+ D ), Ant( 0 ), Suc( 1 ) )
      ImpRightRule( proofOf( A +: B +: Sequent() :+ C :+ D ), B, D )
      ImpRightRule( proofOf( A +: B +: Sequent() :+ C :+ D ), Imp( A, C ) )

      success
    }

    "refuse to construct a proof" in {
      ImpRightRule( LogicalAxiom( A ), Suc( 0 ), Suc( 1 ) ) must throwAn[LKRuleCreationException]
      ImpRightRule( LogicalAxiom( A ), Ant( 0 ), Ant( 0 ) ) must throwAn[LKRuleCreationException]
      ImpRightRule( LogicalAxiom( B ), A, B ) must throwAn[LKRuleCreationException]
      ImpRightRule( LogicalAxiom( A ), Imp( A, B ) ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val p = ImpRightRule( proofOf( A +: B +: Sequent() :+ C :+ D ), A, D )

      if ( p.mainIndices.length != 1 )
        failure

      val i = p.mainIndices.head

      p.endSequent( i ) must beEqualTo( Imp( A, D ) )
    }

    "correctly return its aux formulas" in {
      val p = ImpRightRule( proofOf( A +: B +: Sequent() :+ C :+ D ), A, D )

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
      val p = ImpRightRule( proofOf( A +: B +: C +: Sequent() :+ D :+ E :+ F ), Imp( B, E ) )

      val o = p.getSequentConnector

      testParents( o, "→:r" )(
        p.endSequent,
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Ant( 1 ), Suc( 1 ) ) )

      testChildren( o, "→:r" )(
        p.premise,
        Seq( Ant( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Ant( 1 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Suc( 1 ) ) )
    }
  }

  "ForallRightRule" should {
    "correctly construct a proof" in {
      val ax = proofOf( Sequent() :+ P( alpha ) :+ P( x ) )
      ForallRightRule( ax, Suc( 0 ), alpha, x )
      ForallRightRule( ax, All( x, P( x ) ), alpha )
      ForallRightRule( ax, All( x, P( x ) ) )

      success
    }

    "refuse to construct a proof" in {
      val ax = proofOf( P( alpha ) +: Sequent() :+ P( alpha ) :+ P( x ) )

      ForallRightRule( ax, Ant( 0 ), alpha, x ) must throwAn[LKRuleCreationException]
      ForallRightRule( ax, Suc( 2 ), alpha, x ) must throwAn[LKRuleCreationException]
      ForallRightRule( ax, Suc( 0 ), alpha, x ) must throwAn[LKRuleCreationException]
      ForallRightRule( ax, P( x ), alpha ) must throwAn[LKRuleCreationException]
      ForallRightRule( ax, All( x, P( x ) ), y ) must throwAn[LKRuleCreationException]
      ForallRightRule( ax, All( y, P( y ) ) ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val ax = proofOf( Sequent() :+ P( alpha ) :+ P( x ) )

      val p = ForallRightRule( ax, Suc( 0 ), alpha, x )

      if ( p.mainIndices.length != 1 )
        failure

      p.mainFormulas.head must beEqualTo( All( x, P( x ) ) )
    }

    "correctly return its aux formula" in {
      val ax = proofOf( Sequent() :+ P( alpha ) :+ P( x ) )

      val p = ForallRightRule( ax, Suc( 0 ), alpha, x )

      if ( p.auxIndices.length != 1 )
        failure

      if ( p.auxIndices.head.length != 1 )
        failure

      p.auxFormulas.head.head must beEqualTo( P( alpha ) )
    }

    "correctly connect occurrences" in {
      val ax = proofOf( A +: Sequent() :+ B :+ P( alpha ) :+ C )

      // end sequent of p: A :- B, C, ∀x.P
      val p = ForallRightRule( ax, All( x, P( x ) ), alpha )

      val o = p.getSequentConnector

      testChildren( o, "∀:r" )(
        p.premise,
        Seq( Ant( 0 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Suc( 1 ) ) )

      testParents( o, "∀:r" )(
        p.endSequent,
        Seq( Ant( 0 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Suc( 1 ) ) )
    }
  }

  "ExistsLeftRule" should {
    "correctly construct a proof" in {
      val ax = proofOf( P( alpha ) +: P( x ) +: Sequent() )
      ExistsLeftRule( ax, Ant( 0 ), alpha, x )
      ExistsLeftRule( ax, Ex( x, P( x ) ), alpha )
      ExistsLeftRule( ax, Ex( x, P( x ) ) )

      success
    }

    "refuse to construct a proof" in {
      val ax = proofOf( P( alpha ) +: P( x ) +: Sequent() :+ P( alpha ) )

      ExistsLeftRule( ax, Suc( 0 ), alpha, x ) must throwAn[LKRuleCreationException]
      ExistsLeftRule( ax, Ant( 2 ), alpha, x ) must throwAn[LKRuleCreationException]
      ExistsLeftRule( ax, Suc( 0 ), alpha, x ) must throwAn[LKRuleCreationException]
      ExistsLeftRule( ax, P( x ), alpha ) must throwAn[LKRuleCreationException]
      ExistsLeftRule( ax, Ex( x, P( x ) ), y ) must throwAn[LKRuleCreationException]
      ExistsLeftRule( ax, Ex( y, P( y ) ) ) must throwAn[LKRuleCreationException]
    }

    "correctly return its main formula" in {
      val ax = proofOf( P( alpha ) +: P( x ) +: Sequent() )

      val p = ExistsLeftRule( ax, Ant( 0 ), alpha, x )

      if ( p.mainIndices.length != 1 )
        failure

      p.mainFormulas.head must beEqualTo( Ex( x, P( x ) ) )
    }

    "correctly return its aux formula" in {
      val ax = proofOf( P( alpha ) +: P( x ) +: Sequent() )

      val p = ExistsLeftRule( ax, Ant( 0 ), alpha, x )

      if ( p.auxIndices.length != 1 )
        failure

      if ( p.auxIndices.head.length != 1 )
        failure

      p.auxFormulas.head.head must beEqualTo( P( alpha ) )
    }

    "correctly connect occurrences" in {
      val ax = proofOf( A +: P( alpha ) +: B +: Sequent() :+ C )

      // end sequent of p: ∀x.P, A, B :- C
      val p = ExistsLeftRule( ax, Ex( x, P( x ) ), alpha )

      val o = p.getSequentConnector

      testChildren( o, "∃:l" )(
        p.premise,
        Seq( Ant( 1 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),

        Seq( Suc( 0 ) ) )

      testParents( o, "∃:l" )(
        p.endSequent,
        Seq( Ant( 1 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 2 ) ),

        Seq( Suc( 0 ) ) )
    }
  }

  "EqualityLeftRule" should {
    "correctly construct a proof" in {
      val ax = proofOf( Eq( c, d ) +: Pc +: Pd +: Sequent() :+ Pc :+ Pd )

      EqualityLeftRule( ax, Ant( 0 ), Ant( 1 ), le"λx P(x): o".asInstanceOf[Abs] )
      EqualityLeftRule( ax, Ant( 0 ), Ant( 2 ), le"λx P(x): o".asInstanceOf[Abs] )
      EqualityLeftRule( ax, Eq( c, d ), Pc, Pd )
      EqualityLeftRule( ax, Eq( c, d ), Pd, Pc )

      success
    }

    "refuse to construct a proof" in {
      val ax = proofOf( Eq( c, d ) +: P( x ) +: A +: Sequent() :+ B :+ P( y ) )

      EqualityLeftRule( ax, Ant( 0 ), Ant( 1 ), le"λx P(x): o".asInstanceOf[Abs] ) must throwAn[Exception]
      EqualityLeftRule( ax, Suc( 0 ), Ant( 1 ), le"λx P(x): o".asInstanceOf[Abs] ) must throwAn[Exception]
      EqualityLeftRule( ax, Ant( 0 ), Suc( 1 ), le"λx P(x): o".asInstanceOf[Abs] ) must throwAn[Exception]
      EqualityLeftRule( ax, Ant( 3 ), Ant( 1 ), le"λx P(x): o".asInstanceOf[Abs] ) must throwAn[Exception]
      EqualityLeftRule( ax, Ant( 0 ), Ant( 3 ), le"λx P(x): o".asInstanceOf[Abs] ) must throwAn[Exception]
      EqualityLeftRule( ax, Ant( 2 ), Ant( 1 ), le"λx P(x): o".asInstanceOf[Abs] ) must throwAn[Exception]
      EqualityLeftRule( ax, Suc( 0 ), Ant( 1 ), le"λx P(x): o".asInstanceOf[Abs] ) must throwAn[Exception]
    }

    "correctly return its main formula" in {
      val ax = proofOf( Eq( c, d ) +: Pc +: Pd +: Sequent() :+ Pc :+ Pd )

      val proofs = for ( ( i, f ) <- List( Ant( 1 ) -> Pd, Ant( 2 ) -> Pc ) ) yield ( EqualityLeftRule( ax, Ant( 0 ), i, le"λx P(x): o".asInstanceOf[Abs] ), f )

      for ( ( p, f ) <- proofs ) {
        if ( p.mainIndices.length != 1 )
          failure

        p.mainFormulas.head must beEqualTo( f )
      }

      success
    }

    "correctly return its aux formulas" in {
      val ax = proofOf( Eq( c, d ) +: Pc +: Pd +: Sequent() :+ Pc :+ Pd )

      val proofs = for ( ( i, f ) <- List( Ant( 1 ) -> Pc, Ant( 2 ) -> Pd ) ) yield ( EqualityLeftRule( ax, Ant( 0 ), i, le"λx P(x): o".asInstanceOf[Abs] ), f )

      for ( ( p, f ) <- proofs ) {
        if ( p.auxIndices.length != 1 )
          failure

        if ( p.auxIndices.head.length != 2 )
          failure

        p.auxFormulas.head.head must beEqualTo( Eq( c, d ) )
        p.auxFormulas.head.tail.head must beEqualTo( f )
      }

      success
    }

    "correctly connect occurrences" in {
      val ax = proofOf( A +: Eq( c, d ) +: B +: Pc +: C +: Sequent() :+ D :+ Pd :+ E )

      // end sequent of p1: P(d), A, c = d, B, C :- D, P(d), E
      val p = EqualityLeftRule( ax, Ant( 1 ), Ant( 3 ), le"λx P(x): o".asInstanceOf[Abs] )

      val o = p.getSequentConnector

      testChildren( o, "eq" )(
        p.premise,
        Seq( Ant( 1 ) ),
        Seq( Ant( 2 ) ),
        Seq( Ant( 3 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 4 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 1 ) ),
        Seq( Suc( 2 ) ) )

      testParents( o, "eq" )(
        p.endSequent,
        Seq( Ant( 3 ) ),
        Seq( Ant( 0 ) ),
        Seq( Ant( 1 ) ),
        Seq( Ant( 2 ) ),
        Seq( Ant( 4 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 1 ) ),
        Seq( Suc( 2 ) ) )
    }
  }

  "EqualityRightRule" should {
    "correctly construct a proof" in {
      val ax = proofOf( Eq( c, d ) +: Pc +: Pd +: Sequent() :+ Pc :+ Pd )

      EqualityRightRule( ax, Ant( 0 ), Suc( 0 ), le"λx P(x): o".asInstanceOf[Abs] )
      EqualityRightRule( ax, Ant( 0 ), Suc( 1 ), le"λx P(x): o".asInstanceOf[Abs] )
      EqualityRightRule( ax, Eq( c, d ), Pc, Pd )
      EqualityRightRule( ax, Eq( c, d ), Pd, Pc )

      success
    }

    "refuse to construct a proof" in {
      val ax = proofOf( Eq( c, d ) +: P( x ) +: A +: Sequent() :+ B :+ P( y ) )

      EqualityRightRule( ax, Ant( 0 ), Ant( 1 ), le"λx P(x): o".asInstanceOf[Abs] ) must throwAn[Exception]
      EqualityRightRule( ax, Suc( 0 ), Ant( 1 ), le"λx P(x): o".asInstanceOf[Abs] ) must throwAn[Exception]
      EqualityRightRule( ax, Ant( 0 ), Suc( 1 ), le"λx P(x): o".asInstanceOf[Abs] ) must throwAn[Exception]
      EqualityRightRule( ax, Ant( 3 ), Ant( 1 ), le"λx P(x): o".asInstanceOf[Abs] ) must throwAn[Exception]
      EqualityRightRule( ax, Ant( 0 ), Ant( 3 ), le"λx P(x): o".asInstanceOf[Abs] ) must throwAn[Exception]
      EqualityRightRule( ax, Ant( 2 ), Ant( 1 ), le"λx P(x): o".asInstanceOf[Abs] ) must throwAn[Exception]
      EqualityRightRule( ax, Suc( 0 ), Ant( 1 ), le"λx P(x): o".asInstanceOf[Abs] ) must throwAn[Exception]
    }

    "correctly return its main formula" in {
      val ax = proofOf( Eq( c, d ) +: Pc +: Pd +: Sequent() :+ Pc :+ Pd )

      val proofs = for ( ( i, f ) <- List( Suc( 0 ) -> Pd, Suc( 1 ) -> Pc ) ) yield ( EqualityRightRule( ax, Ant( 0 ), i, le"λx P(x): o".asInstanceOf[Abs] ), f )

      for ( ( p, f ) <- proofs ) {
        if ( p.mainIndices.length != 1 )
          failure

        p.mainFormulas.head must beEqualTo( f )
      }

      success
    }

    "correctly return its aux formulas" in {
      val ax = proofOf( Eq( c, d ) +: Pc +: Pd +: Sequent() :+ Pc :+ Pd )

      val proofs = for ( ( i, f ) <- List( Suc( 0 ) -> Pc, Suc( 1 ) -> Pd ) ) yield ( EqualityRightRule( ax, Ant( 0 ), i, le"λx P(x): o".asInstanceOf[Abs] ), f )

      for ( ( p, f ) <- proofs ) {
        if ( p.auxIndices.length != 1 )
          failure

        if ( p.auxIndices.head.length != 2 )
          failure

        p.auxFormulas.head.head must beEqualTo( Eq( c, d ) )
        p.auxFormulas.head.tail.head must beEqualTo( f )
      }

      success
    }

    "correctly connect occurrences" in {
      val ax = proofOf( A +: Eq( c, d ) +: B +: Pc +: C +: Sequent() :+ D :+ Pd :+ E )

      // end sequent of p2: A, c = d, B, C :- D, E, P(c)
      val p = EqualityRightRule( ax, Ant( 1 ), Suc( 1 ), le"λx P(x): o".asInstanceOf[Abs] )

      val o = p.getSequentConnector

      testChildren( o, "eq" )(
        p.premise,
        Seq( Ant( 0 ) ),
        Seq( Ant( 1 ) ),
        Seq( Ant( 2 ) ),
        Seq( Ant( 3 ) ),
        Seq( Ant( 4 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Suc( 1 ) ) )

      testParents( o, "eq" )(
        p.endSequent,
        Seq( Ant( 0 ) ),
        Seq( Ant( 1 ) ),
        Seq( Ant( 2 ) ),
        Seq( Ant( 3 ) ),
        Seq( Ant( 4 ) ),

        Seq( Suc( 0 ) ),
        Seq( Suc( 2 ) ),
        Seq( Suc( 1 ) ) )
    }
  }

  "The induction rule" should {
    val zero = FOLConst( "0" )
    val Sx = FOLFunction( "s", List( x ) )

    val P0y = FOLAtom( "P", List( zero, y ) )
    val Pxy = FOLAtom( "P", List( x, y ) )
    val PSxy = FOLAtom( "P", List( Sx, y ) )

    "correctly construct a small induction proof" in {
      val ax1 = LogicalAxiom( P0y )

      val ax2 = proofOf( Pxy +: Sequent() :+ PSxy )

      InductionRule(
        Seq(
          InductionCase( ax1, FOLConst( "0" ), Seq(), Seq(), Suc( 0 ) ),
          InductionCase( ax2, FOLFunctionConst( "s", 1 ), Seq( Ant( 0 ) ), Seq( x ), Suc( 0 ) ) ),
        Abs( x, Pxy ), x )

      success
    }

  }

  "exchange rules" should {
    val Seq( a, b ) = Seq( "a", "b" ) map { FOLAtom( _ ) }
    "ExchangeLeftMacroRule" in {
      val p1 = LogicalAxiom( a )
      val p2 = WeakeningLeftRule( p1, b )
      val p3 = ExchangeLeftMacroRule( p2, Ant( 1 ) )
      p3.endSequent must_== ( a +: b +: Sequent() :+ a )
    }
    "ExchangeRightMacroRule" in {
      val p1 = LogicalAxiom( a )
      val p2 = WeakeningRightRule( p1, b )
      val p3 = ExchangeRightMacroRule( p2, Suc( 0 ) )
      p3.endSequent must_== ( a +: Sequent() :+ b :+ a )
    }
  }

  "weakening and contraction macro rules" should {
    "reach a sequent" in {
      val a = FOLAtom( "a" )

      val desiredES = a +: a +: Sequent() :+ a :+ a
      WeakeningContractionMacroRule( LogicalAxiom( a ), desiredES, strict = true ).endSequent must_== desiredES
    }
  }

  "equality left rule eqInConclusion" in {
    val elr = ProofBuilder.
      c( LogicalAxiom( hof"a=b" ) ).
      u( WeakeningLeftRule( _, hof"b=c" ) ).
      u( EqualityLeftRule( _, hof"a=b", hof"b=c", hof"a=c" ) ).
      qed.asInstanceOf[EqualityLeftRule]
    elr.conclusion( elr.eqInConclusion ) must_== hof"a=b"
  }

  "Issue #650" should {
    "be fixed for ∀" in {
      val p1 = ProofLink( foc"th", hos":- P(y,y)" )
      ForallRightRule( p1, fof"!x P(x,y)", fov"y" ) must throwAn[LKRuleCreationException]
    }

    "be fixed for ∃" in {
      val p1 = ProofLink( foc"th", hos"P(y,y) :-" )
      ExistsLeftRule( p1, fof"?x P(x,y)", fov"y" ) must throwAn[LKRuleCreationException]
    }
  }
}
