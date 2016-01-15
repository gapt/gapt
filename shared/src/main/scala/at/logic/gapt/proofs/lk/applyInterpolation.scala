package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs._
import at.logic.gapt.provers.Prover
import at.logic.gapt.expr.To

class InterpolationException( msg: String ) extends Exception( msg )

object ExtractInterpolant {
  def apply( p: LKProof, isPositive: Sequent[Boolean] ) =
    Interpolate( p, isPositive indicesWhere { _ == false }, isPositive indicesWhere { _ == true } )

  def apply( p: LKProof, npart: Seq[SequentIndex], ppart: Seq[SequentIndex] ) = Interpolate( p, npart, ppart )._3

  /**
   * Given sequents negative: \Gamma |- \Delta and positive: \Pi |- \Lambda,
   * compute a proof of \Gamma, \Pi |- \Delta, \Lambda and from that proof,
   * extract an interpolant I such that \Gamma |- \Delta, I and I, \Pi |- \Lambda
   * are valid.
   */
  def apply( negative: HOLSequent, positive: HOLSequent, prover: Prover ): HOLFormula = {
    val seq = negative ++ positive
    val p = prover.getLKProof( seq ).get

    val npart = p.endSequent.filter { fo => negative.contains( fo ) }
    val ppart = p.endSequent.filter { fo => positive.contains( fo ) }

    apply( p, npart.indices, ppart.indices )
  }
}

object Interpolate {
  /**
   * This method computes interpolating proofs from propositional LK-proof
   * containing at most atomic cuts. As arguments it expects a proof p
   * and a partition of its end-sequent into two parts:
   * a "negative" part and a "positive" part.
   * For \Gamma |- \Delta being the negative and \Pi |- \Lambda being the
   * positive part, it will compute an interpolant I and proofs of
   * \Gamma |- \Delta, I and I, \Pi |- \Lambda
   *
   * @param p     the LK proof from which the interpolant is to be extracted
   * @param npart the negative part of the partition of the end-sequent of p
   * @param ppart the positive part of the partition of the end-sequent of p
   * @return      a triple consisting of ( a proof of \Gamma |- \Delta, I,
   *              a proof of I, \Pi |- \Lambda, the FOLFormula I )
   * @throws InterpolationException if the input proof is not propositional,
   *         contains non-atomic cuts or if (npart,ppart) is not a partition of its
   *         end-sequent.
   */
  def apply( p: LKProof, npart: Seq[SequentIndex], ppart: Seq[SequentIndex] ): ( LKProof, LKProof, HOLFormula ) = p match {

    // axioms

    case LogicalAxiom( atom ) => {
      assert( npart.size + ppart.size == 2 )
      val inNpart = npart.filter( ind => p.endSequent( ind ) == atom )
      val inPpart = ppart.filter( ind => p.endSequent( ind ) == atom )

      /*
       * Distinguish cases according to the partitions of the formulas in the logical axiom:
       * Case: A :- A and :-   => Interpolant: ⊥   =>   Result: A :- A,⊥ and ⊥ :-
       * 
       * Case: :- and A :- A   => Interpolant: ⊤   =>   Result: :- ⊤ and ⊤,A :- A
       * 
       * Case: :- A and A :-   => Interpolant: ¬A  =>   Result: :- A,¬A and ¬A,A :-
       * 
       * Case: A :- and :- A   => Interpolant: A   =>   Result: A :- A and A :- A
       */
      if ( inNpart.size == 2 ) ( WeakeningRightRule( p, Bottom() ), Axiom( Bottom() :: Nil, Nil ), Bottom() )
      else if ( inNpart.size == 1 && inPpart.size == 1 ) {
        if ( inNpart( 0 ).isInstanceOf[Ant] && inPpart( 0 ).isInstanceOf[Suc] ) ( p, p, atom )
        else if ( inNpart( 0 ).isInstanceOf[Suc] && inPpart( 0 ).isInstanceOf[Ant] ) ( NegRightRule( p, atom ), NegLeftRule( p, atom ), Neg( atom ) )
        else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
      } else if ( inPpart.size == 2 ) ( Axiom( Nil, Top() :: Nil ), WeakeningLeftRule( p, Top() ), Top() )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    /*
     * Possible partitions
     * 
     * Case: :- ⊤ and :-  => Interpolant: ⊥   =>  Result: :- ⊤,⊥ and ⊥ :-
     * 
     * Case: :- and :- ⊤  => Interpolant: ⊤   =>  Result: :- ⊤ and ⊤ :- ⊤
     */
    case TopAxiom => {
      assert( npart.size + ppart.size == 1 )
      val inNpart = npart.filter( ind => p.endSequent( ind ) == Top() )
      val inPpart = ppart.filter( ind => p.endSequent( ind ) == Top() )

      if ( inNpart.size == 1 ) ( WeakeningRightRule( p, Bottom() ), Axiom( Bottom() :: Nil, Nil ), Bottom() )
      else if ( inPpart.size == 1 ) ( Axiom( Nil, Top() :: Nil ), WeakeningLeftRule( p, Top() ), Top() )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    /*
     * Possible Partitions:
     * 
     * Case: ⊥ :- and :-  => Interpolant: ⊥   =>  Result: ⊥ :- ⊥ and ⊥ :-
     * 
     * Case: :- and ⊥ :-  => Interpolant: ⊤   =>  Result: :- ⊤ and ⊤,⊥ :-
     */
    case BottomAxiom => {
      assert( npart.size + ppart.size == 1 )
      val inNpart = npart.filter( ind => p.endSequent( ind ) == Bottom() )
      val inPpart = ppart.filter( ind => p.endSequent( ind ) == Bottom() )

      if ( inNpart.size == 1 ) ( WeakeningRightRule( p, Bottom() ), Axiom( Bottom() :: Nil, Nil ), Bottom() )
      else if ( inPpart.size == 1 ) ( Axiom( Nil, Top() :: Nil ), WeakeningLeftRule( p, Top() ), Top() )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    /*
     * Possible Partitions:
     * 
     * Case: :- s=s and :-  => Interpolant: ⊥   =>  Result: :- s=s,⊥ and ⊥ :-
     * 
     * Case: :- and :- s=s  => Interpolant: ⊤   =>  Result: :- ⊤ and ⊤ :- s=s
     */
    case ReflexivityAxiom( term ) => {
      assert( npart.size + ppart.size == 1 )
      val atom = Eq( term, term )
      val inNpart = npart.filter( ind => p.endSequent( ind ) == atom )
      val inPpart = ppart.filter( ind => p.endSequent( ind ) == atom )

      if ( inNpart.size == 1 ) ( WeakeningRightRule( p, Bottom() ), Axiom( Bottom() :: Nil, Nil ), Bottom() )
      else if ( inPpart.size == 1 ) ( Axiom( Nil, Top() :: Nil ), WeakeningLeftRule( p, Top() ), Top() )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    // structural rules

    case WeakeningLeftRule( subProof, formula ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )
      val inNpart = npart.filter( ind => p.endSequent.indices.contains( ind ) )
      val inPpart = ppart.filter( ind => p.endSequent.indices.contains( ind ) )

      // p.mainIndices refers to the index of the formula introduced by WeakeningLeft in the end-sequent of the proof p
      if ( npart.contains( p.mainIndices( 0 ) ) ) ( WeakeningLeftRule( up_nproof, formula ), up_pproof, up_I )
      else if ( ppart.contains( p.mainIndices( 0 ) ) ) ( up_nproof, WeakeningLeftRule( up_pproof, formula ), up_I )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case WeakeningRightRule( subProof, formula ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      if ( npart.contains( p.mainIndices( 0 ) ) ) ( WeakeningRightRule( up_nproof, formula ), up_pproof, up_I )
      else if ( ppart.contains( p.mainIndices( 0 ) ) ) ( up_nproof, WeakeningRightRule( up_pproof, formula ), up_I )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case ContractionLeftRule( subProof, aux1, aux2 ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )
      val formula = p.mainFormulas( 0 )

      if ( npart.contains( p.mainIndices( 0 ) ) ) ( ContractionLeftRule( up_nproof, formula ), up_pproof, up_I )
      else if ( ppart.contains( p.mainIndices( 0 ) ) ) ( up_nproof, ContractionLeftRule( up_pproof, formula ), up_I )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case ContractionRightRule( subProof, aux1, aux2 ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )
      val formula = p.mainFormulas( 0 )

      if ( npart.contains( p.mainIndices( 0 ) ) ) ( ContractionRightRule( up_nproof, formula ), up_pproof, up_I )
      else if ( ppart.contains( p.mainIndices( 0 ) ) ) ( up_nproof, ContractionRightRule( up_pproof, formula ), up_I )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) => {
      val ( up1_nproof, up1_pproof, up1_I ) = applyUpCutLeft( p, npart, ppart, aux1 )
      val ( up2_nproof, up2_pproof, up2_I ) = applyUpCutRight( p, npart, ppart, aux2 )

      val up1_nFormulas = up1_nproof.endSequent.formulas
      val up2_nFormulas = up2_nproof.endSequent.formulas
      val up1_pFormulas = up1_pproof.endSequent.formulas
      val up2_pFormulas = up2_pproof.endSequent.formulas
      val cutFormula = p.auxFormulas( 0 )( 0 )

      if ( ( up1_nFormulas.contains( cutFormula ) && up2_nFormulas.contains( cutFormula ) ) ) {
        val ipl = Or( up1_I, up2_I )
        val np = OrRightRule( CutRule( up1_nproof, cutFormula, up2_nproof, cutFormula ), up1_I, up2_I )
        val pp = OrLeftRule( up1_pproof, up1_I, up2_pproof, up2_I )

        ( np, pp, ipl )
      } else if ( ( up1_pFormulas.contains( cutFormula ) && up2_pFormulas.contains( cutFormula ) ) ) {
        val ipl = And( up1_I, up2_I )
        val np = AndRightRule( up1_nproof, up1_I, up2_nproof, up2_I )
        val pp = AndLeftRule( CutRule( up1_pproof, cutFormula, up2_pproof, cutFormula ), up1_I, up2_I )

        ( np, pp, ipl )
      } else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    // propositional rules

    case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) => {
      val ( up1_nproof, up1_pproof, up1_I ) = applyUpBinaryLeft( p, npart, ppart )
      val ( up2_nproof, up2_pproof, up2_I ) = applyUpBinaryRight( p, npart, ppart )
      val formula1 = p.auxFormulas( 0 )( 0 )
      val formula2 = p.auxFormulas( 1 )( 0 )

      if ( npart.contains( p.mainIndices( 0 ) ) ) {
        val ipl = Or( up1_I, up2_I )
        val np = OrRightRule( AndRightRule( up1_nproof, formula1, up2_nproof, formula2 ), up1_I, up2_I )
        val pp = OrLeftRule( up1_pproof, up1_I, up2_pproof, up2_I )

        ( np, pp, ipl )
      } else if ( ppart.contains( p.mainIndices( 0 ) ) ) {
        val ipl = And( up1_I, up2_I )
        val np = AndRightRule( up1_nproof, up1_I, up2_nproof, up2_I )
        val pp = AndLeftRule( AndRightRule( up1_pproof, formula1, up2_pproof, formula2 ), up1_I, up2_I )

        ( np, pp, ipl )
      } else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case AndLeftRule( subProof, aux1, aux2 ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )
      val formula1 = p.auxFormulas( 0 )( 0 )
      val formula2 = p.auxFormulas( 0 )( 1 )

      if ( npart.contains( p.mainIndices( 0 ) ) ) ( AndLeftRule( up_nproof, formula1, formula2 ), up_pproof, up_I )
      else if ( ppart.contains( p.mainIndices( 0 ) ) ) ( up_nproof, AndLeftRule( up_pproof, formula1, formula2 ), up_I )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) => {
      val ( up1_nproof, up1_pproof, up1_I ) = applyUpBinaryLeft( p, npart, ppart )
      val ( up2_nproof, up2_pproof, up2_I ) = applyUpBinaryRight( p, npart, ppart )
      val formula1 = p.auxFormulas( 0 )( 0 )
      val formula2 = p.auxFormulas( 1 )( 0 )

      if ( npart.contains( p.mainIndices( 0 ) ) ) {
        val ipl = Or( up1_I, up2_I )
        val np = OrRightRule( OrLeftRule( up1_nproof, formula1, up2_nproof, formula2 ), up1_I, up2_I )
        val pp = OrLeftRule( up1_pproof, up1_I, up2_pproof, up2_I )

        ( np, pp, ipl )
      } else if ( ppart.contains( p.mainIndices( 0 ) ) ) {
        val ipl = And( up1_I, up2_I )
        val np = AndRightRule( up1_nproof, up1_I, up2_nproof, up2_I )
        val pp = AndLeftRule( OrLeftRule( up1_pproof, formula1, up2_pproof, formula2 ), up1_I, up2_I )

        ( np, pp, ipl )
      } else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case OrRightRule( subProof, aux1, aux2 ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )
      val formula1 = p.auxFormulas( 0 )( 0 )
      val formula2 = p.auxFormulas( 0 )( 1 )

      if ( npart.contains( p.mainIndices( 0 ) ) ) ( OrRightRule( up_nproof, formula1, formula2 ), up_pproof, up_I )
      else if ( ppart.contains( p.mainIndices( 0 ) ) ) ( up_nproof, OrRightRule( up_pproof, formula1, formula2 ), up_I )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case NegLeftRule( subProof, aux ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      if ( npart.contains( p.mainIndices( 0 ) ) ) ( NegLeftRule( up_nproof, subProof.endSequent( aux ) ), up_pproof, up_I )
      else if ( ppart.contains( p.mainIndices( 0 ) ) ) ( up_nproof, NegLeftRule( up_pproof, subProof.endSequent( aux ) ), up_I )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case NegRightRule( subProof, aux ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      if ( npart.contains( p.mainIndices( 0 ) ) ) ( NegRightRule( up_nproof, subProof.endSequent( aux ) ), up_pproof, up_I )
      else if ( ppart.contains( p.mainIndices( 0 ) ) ) ( up_nproof, NegRightRule( up_pproof, subProof.endSequent( aux ) ), up_I )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) => {
      val ( up1_nproof, up1_pproof, up1_I ) = applyUpBinaryLeft( p, npart, ppart )
      val ( up2_nproof, up2_pproof, up2_I ) = applyUpBinaryRight( p, npart, ppart )
      val formula1 = p.auxFormulas( 0 )( 0 )
      val formula2 = p.auxFormulas( 1 )( 0 )

      if ( npart.contains( p.mainIndices( 0 ) ) ) {
        val ipl = Or( up1_I, up2_I )
        val np = OrRightRule( ImpLeftRule( up1_nproof, formula1, up2_nproof, formula2 ), up1_I, up2_I )
        val pp = OrLeftRule( up1_pproof, up1_I, up2_pproof, up2_I )

        ( np, pp, ipl )
      } else if ( ppart.contains( p.mainIndices( 0 ) ) ) {
        val ipl = And( up1_I, up2_I )
        val np = AndRightRule( up1_nproof, up1_I, up2_nproof, up2_I )
        val pp = AndLeftRule( ImpLeftRule( up1_pproof, formula1, up2_pproof, formula2 ), up1_I, up2_I )

        ( np, pp, ipl )
      } else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case ImpRightRule( subProof, aux1, aux2 ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )
      val formula1 = p.auxFormulas( 0 )( 0 )
      val formula2 = p.auxFormulas( 0 )( 1 )

      if ( npart.contains( p.mainIndices( 0 ) ) ) ( ImpRightRule( up_nproof, formula1, formula2 ), up_pproof, up_I )
      else if ( ppart.contains( p.mainIndices( 0 ) ) ) ( up_nproof, ImpRightRule( up_pproof, formula1, formula2 ), up_I )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    // equality rules

    case EqualityRightRule( subProof, eq, aux, pos ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )
      val auxFormula = subProof.endSequent( aux )
      val eqIndex = p.occConnectors( 0 ).child( eq )

      var ipl = up_I

      if ( npart.contains( eqIndex ) && npart.contains( p.mainIndices( 0 ) ) ) ( EqualityRightRule( up_nproof, eq, auxFormula, pos ), up_pproof, up_I )
      else if ( ppart.contains( eqIndex ) && ppart.contains( p.mainIndices( 0 ) ) ) ( up_nproof, EqualityRightRule( up_pproof, eq, auxFormula, pos ), up_I )
      else if ( npart.contains( p.mainIndices( 0 ) ) ) {
        ipl = Imp( p.endSequent( eqIndex ), up_I )

        val up_nproof1 = WeakeningLeftRule( up_nproof, p.endSequent( eqIndex ) )
        val up_nproof2 = EqualityRightRule( up_nproof1, eq, auxFormula, pos )
        val up_nproof3 = ImpRightRule( up_nproof2, p.endSequent( eqIndex ), up_I )

        val up_pproof1 = ImpLeftRule( LogicalAxiom( p.endSequent( eqIndex ) ), p.endSequent( eqIndex ), up_pproof, up_I )
        val up_pproof2 = ContractionLeftRule( up_pproof1, p.endSequent( eqIndex ) )

        ( up_nproof3, up_pproof2, ipl )
      } else if ( ppart.contains( p.mainIndices( 0 ) ) ) {
        ipl = And( p.endSequent( eqIndex ), up_I )

        val up_nproof1 = AndRightRule( LogicalAxiom( p.endSequent( eqIndex ) ), up_nproof, And( p.endSequent( eqIndex ), up_I ) )
        val up_nproof2 = ContractionLeftRule( up_nproof1, p.endSequent( eqIndex ) )

        val up_pproof1 = WeakeningLeftRule( up_pproof, p.endSequent( eqIndex ) )
        val up_pproof2 = EqualityRightRule( up_pproof1, eq, auxFormula, pos )
        val up_pproof3 = AndLeftRule( up_pproof2, p.endSequent( eqIndex ), up_I )

        ( up_nproof2, up_pproof3, ipl )
      } else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case EqualityLeftRule( subProof, eq, aux, pos ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )
      val auxFormula = subProof.endSequent( aux )
      val eqIndex = p.occConnectors( 0 ).child( eq )

      var ipl = up_I

      if ( npart.contains( eqIndex ) && npart.contains( p.mainIndices( 0 ) ) ) ( EqualityLeftRule( up_nproof, eq, auxFormula, pos ), up_pproof, up_I )
      else if ( ppart.contains( eqIndex ) && ppart.contains( p.mainIndices( 0 ) ) ) ( up_nproof, EqualityLeftRule( up_pproof, eq, auxFormula, pos ), up_I )
      else if ( npart.contains( p.mainIndices( 0 ) ) ) {
        ipl = Imp( p.endSequent( eqIndex ), up_I )

        val up_nproof1 = WeakeningLeftRule( up_nproof, p.endSequent( eqIndex ) )
        val up_nproof2 = EqualityLeftRule( up_nproof1, eq, auxFormula, pos )
        val up_nproof3 = ImpRightRule( up_nproof2, p.endSequent( eqIndex ), up_I )

        val up_pproof1 = ImpLeftRule( LogicalAxiom( p.endSequent( eqIndex ) ), p.endSequent( eqIndex ), up_pproof, up_I )
        val up_pproof2 = ContractionLeftRule( up_pproof1, p.endSequent( eqIndex ) )

        ( up_nproof3, up_pproof2, ipl )
      } else if ( ppart.contains( p.mainIndices( 0 ) ) ) {
        ipl = And( p.endSequent( eqIndex ), up_I )

        val up_nproof1 = AndRightRule( LogicalAxiom( p.endSequent( eqIndex ) ), up_nproof, And( p.endSequent( eqIndex ), up_I ) )
        val up_nproof2 = ContractionLeftRule( up_nproof1, p.endSequent( eqIndex ) )

        val up_pproof1 = WeakeningLeftRule( up_pproof, p.endSequent( eqIndex ) )
        val up_pproof2 = EqualityLeftRule( up_pproof1, eq, auxFormula, pos )
        val up_pproof3 = AndLeftRule( up_pproof2, p.endSequent( eqIndex ), up_I )

        ( up_nproof2, up_pproof3, ipl )
      } else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case p @ ForallLeftRule( subProof, aux, main, term, quantVar ) =>
      val ( nproof, pproof, interpolant ) = apply( subProof, npart map p.getOccConnector.parent, ppart map p.getOccConnector.parent )

      if ( npart contains p.mainIndices( 0 ) ) {
        ( ForallLeftRule( nproof, p.mainFormula, term ), pproof, interpolant )
      } else {
        ( nproof, ForallLeftRule( pproof, p.mainFormula, term ), interpolant )
      }

    case p @ ExistsRightRule( subProof, aux, main, term, quantVar ) =>
      val ( nproof, pproof, interpolant ) = apply( subProof, npart map p.getOccConnector.parent, ppart map p.getOccConnector.parent )

      if ( npart contains p.mainIndices( 0 ) ) {
        ( ExistsRightRule( nproof, p.mainFormula, term ), pproof, interpolant )
      } else {
        ( nproof, ExistsRightRule( pproof, p.mainFormula, term ), interpolant )
      }

    case _ => throw new InterpolationException( "Unknown inference rule of type: " + p.name.toString() + "." )
  }

  private def applyUpUnary( p: LKProof, npart: Seq[SequentIndex], ppart: Seq[SequentIndex] ) = {
    val up_npart = npart.flatMap { ind => p.occConnectors( 0 ).parents( ind ) }
    val up_ppart = ppart.flatMap { ind => p.occConnectors( 0 ).parents( ind ) }

    apply( p.immediateSubProofs( 0 ), up_npart, up_ppart )
  }

  private def applyUpBinaryLeft( p1: LKProof, npart: Seq[SequentIndex], ppart: Seq[SequentIndex] ) = {
    val up_npart = npart.flatMap { ind => p1.occConnectors( 0 ).parents( ind ) }
    val up_ppart = ppart.flatMap { ind => p1.occConnectors( 0 ).parents( ind ) }

    apply( p1.immediateSubProofs( 0 ), up_npart, up_ppart )
  }

  private def applyUpBinaryRight( p2: LKProof, npart: Seq[SequentIndex], ppart: Seq[SequentIndex] ) = {
    val up_npart = npart.flatMap { ind => p2.occConnectors( 1 ).parents( ind ) }
    val up_ppart = ppart.flatMap { ind => p2.occConnectors( 1 ).parents( ind ) }

    apply( p2.immediateSubProofs( 1 ), up_npart, up_ppart )
  }

  private def applyUpCutLeft( p1: LKProof, npart: Seq[SequentIndex], ppart: Seq[SequentIndex], aux1: SequentIndex ) = {
    var up_npart = npart.flatMap { ind => p1.occConnectors( 0 ).parents( ind ) }
    var up_ppart = ppart.flatMap { ind => p1.occConnectors( 0 ).parents( ind ) }

    val auxFormula = p1.immediateSubProofs( 0 ).endSequent( aux1 )
    val nFormulas = npart.filter { ind => p1.endSequent( ind ) == auxFormula }
    val pFormulas = ppart.filter { ind => p1.endSequent( ind ) == auxFormula }

    if ( !pFormulas.isEmpty && nFormulas.isEmpty ) {
      up_ppart :+= aux1
    } else {
      up_npart :+= aux1
    }

    apply( p1.immediateSubProofs( 0 ), up_npart, up_ppart )
  }

  private def applyUpCutRight( p2: LKProof, npart: Seq[SequentIndex], ppart: Seq[SequentIndex], aux2: SequentIndex ) = {
    var up_npart = npart.flatMap { ind => p2.occConnectors( 1 ).parents( ind ) }
    var up_ppart = ppart.flatMap { ind => p2.occConnectors( 1 ).parents( ind ) }

    val auxFormula = p2.immediateSubProofs( 1 ).endSequent( aux2 )
    val nFormulas = npart.filter { ind => p2.endSequent( ind ) == auxFormula }
    val pFormulas = ppart.filter { ind => p2.endSequent( ind ) == auxFormula }

    if ( !pFormulas.isEmpty && nFormulas.isEmpty ) {
      up_ppart :+= aux2
    } else {
      up_npart :+= aux2
    }

    apply( p2.immediateSubProofs( 1 ), up_npart, up_ppart )
  }

}

