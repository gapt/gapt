package at.logic.gapt.proofs.lkOld

import at.logic.gapt.expr._
import at.logic.gapt.proofs.HOLSequent
import at.logic.gapt.proofs.lkOld.base._
import at.logic.gapt.proofs.lkOld._
import at.logic.gapt.proofs.lk.lkNew2Old
import at.logic.gapt.proofs.occurrences._
import at.logic.gapt.provers.Prover
import at.logic.gapt.expr.To

class InterpolationException( msg: String ) extends Exception( msg )

object ExtractInterpolant {
  def apply( p: LKProof, npart: Set[FormulaOccurrence], ppart: Set[FormulaOccurrence] ) = Interpolate( p, npart, ppart )._3

  /**
   * Given sequents negative: \Gamma |- \Delta and positive: \Pi |- \Lambda,
   * compute a proof of \Gamma, \Pi |- \Delta, \Lambda and from that proof,
   * extract an interpolant I such that \Gamma |- \Delta, I and I, \Pi |- \Lambda
   * are valid.
   */
  def apply( negative: HOLSequent, positive: HOLSequent, prover: Prover ): FOLFormula = {
    val seq = negative ++ positive
    val p = lkNew2Old( prover.getLKProof( seq ).get )
    val es = p.root
    val npart = es.antecedent.filter( fo => negative.antecedent.contains( fo.formula ) ) ++
      es.succedent.filter( fo => negative.succedent.contains( fo.formula ) )
    val ppart = es.antecedent.filter( fo => positive.antecedent.contains( fo.formula ) ) ++
      es.succedent.filter( fo => positive.succedent.contains( fo.formula ) )
    apply( p, npart.toSet, ppart.toSet )
  }
}

object Interpolate {
  /**
   * This method computes interpolating proofs from a cut-free propositional
   * LK-proof. As arguments it expects a proof p and a partition of its
   * end-sequent into two parts: a "negative" part and a "positive" part.
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
  def apply( p: LKProof, npart: Set[FormulaOccurrence], ppart: Set[FormulaOccurrence] ): ( LKProof, LKProof, FOLFormula ) = p match {

    case Axiom( s ) => {
      // we assume here that s has exactly one formula in the antecedent and exactly one in the succedent
      // and that these two formulas are identical or that s is an instance of the reflexivity axiom.
      if ( s.antecedent.size == 1 && s.succedent.size == 1 ) {
        val oant = s.antecedent( 0 )
        val osuc = s.succedent( 0 )
        val form = oant.formula

        if ( npart.contains( oant ) && npart.contains( osuc ) ) ( WeakeningRightRule( p, Bottom() ), Axiom( Bottom() :: Nil, Nil ), Bottom() )
        else if ( npart.contains( oant ) && ppart.contains( osuc ) ) ( p, p, form.asInstanceOf[FOLFormula] )
        else if ( ppart.contains( oant ) && npart.contains( osuc ) ) ( NegRightRule( p, form ), NegLeftRule( p, form ), Neg( form.asInstanceOf[FOLFormula] ) )
        else if ( ppart.contains( oant ) && ppart.contains( osuc ) ) ( Axiom( Nil, Top() :: Nil ), WeakeningLeftRule( p, Top() ), Top() )
        else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
      } else if ( s.antecedent.size == 0 && s.succedent.size == 1 ) {
        // here, we handle reflexivity axioms and axioms of the form :- Top()
        val osuc = s.succedent( 0 )

        if ( npart.contains( osuc ) ) ( WeakeningRightRule( p, Bottom() ), Axiom( Bottom() :: Nil, Nil ), Bottom() )
        else if ( ppart.contains( osuc ) ) ( Axiom( Nil, Top() :: Nil ), WeakeningLeftRule( p, Top() ), Top() )
        else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
      } else if ( s.antecedent.size == 1 && s.succedent.size == 0 ) {
        // here, we handle axioms of the form Bottom() :- 
        val oant = s.antecedent( 0 )

        if ( npart.contains( oant ) ) ( WeakeningRightRule( p, Bottom() ), Axiom( Bottom() :: Nil, Nil ), Bottom() )
        else if ( ppart.contains( oant ) ) ( Axiom( Nil, Top() :: Nil ), WeakeningLeftRule( p, Top() ), Top() )
        else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
      } else throw new InterpolationException( "Axiom has context or the rule is not an axiom." )
    }

    // structural rules

    case WeakeningLeftRule( p, s, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      if ( npart.contains( m ) ) ( WeakeningLeftRule( up_nproof, m.formula ), up_pproof, up_I )
      else if ( ppart.contains( m ) ) ( up_nproof, WeakeningLeftRule( up_pproof, m.formula ), up_I )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case WeakeningRightRule( p, s, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      if ( npart.contains( m ) ) ( WeakeningRightRule( up_nproof, m.formula ), up_pproof, up_I )
      else if ( ppart.contains( m ) ) ( up_nproof, WeakeningRightRule( up_pproof, m.formula ), up_I )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case ContractionLeftRule( p, s, a1, a2, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      if ( npart.contains( m ) ) ( ContractionLeftRule( up_nproof, m.formula ), up_pproof, up_I )
      else if ( ppart.contains( m ) ) ( up_nproof, ContractionLeftRule( up_pproof, m.formula ), up_I )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case ContractionRightRule( p, s, a1, a2, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      if ( npart.contains( m ) ) ( ContractionRightRule( up_nproof, m.formula ), up_pproof, up_I )
      else if ( ppart.contains( m ) ) ( up_nproof, ContractionRightRule( up_pproof, m.formula ), up_I )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case CutRule( p1, p2, s, a1, a2 ) => {
      val ( up1_nproof, up1_pproof, up1_I ) = applyUpCutLeft( p1, npart, ppart, a1 )
      val ( up2_nproof, up2_pproof, up2_I ) = applyUpCutRight( p2, s, npart, ppart, a2 )

      val npart1Fold = up1_nproof.root.occurrences.foldLeft( Seq[HOLFormula]() )( ( s, o ) => s :+ o.formula )
      val ppart1Fold = up1_pproof.root.occurrences.foldLeft( Seq[HOLFormula]() )( ( s, o ) => s :+ o.formula )
      val npart2Fold = up2_nproof.root.occurrences.foldLeft( Seq[HOLFormula]() )( ( s, o ) => s :+ o.formula )
      val ppart2Fold = up2_pproof.root.occurrences.foldLeft( Seq[HOLFormula]() )( ( s, o ) => s :+ o.formula )

      if ( npart1Fold.contains( a1.formula ) || npart2Fold.contains( a2.formula )
        && !( ppart1Fold.contains( a1.formula ) || ppart2Fold.contains( a2.formula ) ) ) {
        val ipl = Or( up1_I, up2_I )
        val np = OrRightRule( CutRule( up1_nproof, up2_nproof, a1 ), up1_I, up2_I )
        val pp = OrLeftRule( up1_pproof, up2_pproof, up1_I, up2_I )

        ( np, pp, ipl )

      } else if ( ppart1Fold.contains( a1.formula ) && ppart2Fold.contains( a2.formula )
        && !( npart1Fold.contains( a1.formula ) || npart2Fold.contains( a2.formula ) ) ) {
        val ipl = And( up1_I, up2_I )
        val np = AndRightRule( up1_nproof, up2_nproof, up1_I, up2_I )
        val pp = AndLeftRule( CutRule( up1_pproof, up2_pproof, a1 ), up1_I, up2_I )

        ( np, pp, ipl )

      } else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    // propositional rules

    case AndRightRule( p1, p2, s, a1, a2, m ) => {
      val ( up1_nproof, up1_pproof, up1_I ) = applyUpBinaryLeft( p1, npart, ppart )
      val ( up2_nproof, up2_pproof, up2_I ) = applyUpBinaryRight( p2, npart, ppart )

      if ( npart.contains( m ) ) {
        val ipl = Or( up1_I, up2_I )
        val np = OrRightRule( AndRightRule( up1_nproof, up2_nproof, a1.formula, a2.formula ), up1_I, up2_I )
        val pp = OrLeftRule( up1_pproof, up2_pproof, up1_I, up2_I )

        ( np, pp, ipl )
      } else if ( ppart.contains( m ) ) {
        val ipl = And( up1_I, up2_I )
        val np = AndRightRule( up1_nproof, up2_nproof, up1_I, up2_I )
        val pp = AndLeftRule( AndRightRule( up1_pproof, up2_pproof, a1.formula, a2.formula ), up1_I, up2_I )

        ( np, pp, ipl )
      } else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case AndLeft1Rule( p, s, a, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      m.formula match {
        case And( l, r ) => // TODO - is this possible in a less ugly way, i.e. without matching? -- analogously below
          if ( npart.contains( m ) ) ( AndLeft1Rule( up_nproof, l, r ), up_pproof, up_I )
          else if ( ppart.contains( m ) ) ( up_nproof, AndLeft1Rule( up_pproof, l, r ), up_I )
          else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
      }
    }

    case AndLeft2Rule( p, s, a, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      m.formula match {
        case And( l, r ) =>
          if ( npart.contains( m ) ) ( AndLeft2Rule( up_nproof, l, r ), up_pproof, up_I )
          else if ( ppart.contains( m ) ) ( up_nproof, AndLeft2Rule( up_pproof, l, r ), up_I )
          else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
      }
    }

    case OrLeftRule( p1, p2, s, a1, a2, m ) => {
      val ( up1_nproof, up1_pproof, up1_I ) = applyUpBinaryLeft( p1, npart, ppart )
      val ( up2_nproof, up2_pproof, up2_I ) = applyUpBinaryRight( p2, npart, ppart )

      if ( npart.contains( m ) ) {
        val ipl = Or( up1_I, up2_I )
        val np = OrRightRule( OrLeftRule( up1_nproof, up2_nproof, a1.formula, a2.formula ), up1_I, up2_I )
        val pp = OrLeftRule( up1_pproof, up2_pproof, up1_I, up2_I )

        ( np, pp, ipl )
      } else if ( ppart.contains( m ) ) {
        val ipl = And( up1_I, up2_I )
        val np = AndRightRule( up1_nproof, up2_nproof, up1_I, up2_I )
        val pp = AndLeftRule( OrLeftRule( up1_pproof, up2_pproof, a1.formula, a2.formula ), up1_I, up2_I )

        ( np, pp, ipl )
      } else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case OrRight1Rule( p, s, a, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      m.formula match {
        case Or( l, r ) =>
          if ( npart.contains( m ) ) ( OrRight1Rule( up_nproof, l, r ), up_pproof, up_I )
          else if ( ppart.contains( m ) ) ( up_nproof, OrRight1Rule( up_pproof, l, r ), up_I )
          else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
      }
    }

    case OrRight2Rule( p, s, a, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      m.formula match {
        case Or( l, r ) =>
          if ( npart.contains( m ) ) ( OrRight2Rule( up_nproof, l, r ), up_pproof, up_I )
          else if ( ppart.contains( m ) ) ( up_nproof, OrRight2Rule( up_pproof, l, r ), up_I )
          else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
      }
    }

    case NegLeftRule( p, s, a, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      if ( npart.contains( m ) ) ( NegLeftRule( up_nproof, a.formula ), up_pproof, up_I )
      else if ( ppart.contains( m ) ) ( up_nproof, NegLeftRule( up_pproof, a.formula ), up_I )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case NegRightRule( p, s, a, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      if ( npart.contains( m ) ) ( NegRightRule( up_nproof, a.formula ), up_pproof, up_I )
      else if ( ppart.contains( m ) ) ( up_nproof, NegRightRule( up_pproof, a.formula ), up_I )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case ImpLeftRule( p1, p2, s, a1, a2, m ) => {
      val ( up1_nproof, up1_pproof, up1_I ) = applyUpBinaryLeft( p1, npart, ppart )
      val ( up2_nproof, up2_pproof, up2_I ) = applyUpBinaryRight( p2, npart, ppart )

      if ( npart.contains( m ) ) {
        val ipl = Or( up1_I, up2_I )
        val np = OrRightRule( ImpLeftRule( up1_nproof, up2_nproof, a1.formula, a2.formula ), up1_I, up2_I )
        val pp = OrLeftRule( up1_pproof, up2_pproof, up1_I, up2_I )

        ( np, pp, ipl )
      } else if ( ppart.contains( m ) ) {
        val ipl = And( up1_I, up2_I )
        val np = AndRightRule( up1_nproof, up2_nproof, up1_I, up2_I )
        val pp = AndLeftRule( ImpLeftRule( up1_pproof, up2_pproof, a1.formula, a2.formula ), up1_I, up2_I )

        ( np, pp, ipl )
      } else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case ImpRightRule( p, s, a1, a2, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      if ( npart.contains( m ) ) ( ImpRightRule( up_nproof, a1.formula, a2.formula ), up_pproof, up_I )
      else if ( ppart.contains( m ) ) ( up_nproof, ImpRightRule( up_pproof, a1.formula, a2.formula ), up_I )
      else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    // equality rules

    case EquationRight1Rule( p1, p2, s, a1, a2, pos, m ) => {
      val a1F: FOLFormula = a1.formula.asInstanceOf[FOLFormula]
      val ( up1_nproof, up1_pproof, up1_I ) = applyUpEqualityLeft( p1, a1, npart, ppart, true )
      val ( up2_nproof, up2_pproof, up2_I ) = applyUpBinaryRight( p2, npart, ppart )

      if ( npart.contains( m ) ) {
        val ipl = Or( up1_I, And( a1F, up2_I ) )

        val eqr1 = EquationRight1Rule( Axiom( a1.formula ), up2_nproof, a1.formula, a2.formula, m.formula )
        val andr1 = AndRightRule( Axiom( a1.formula ), eqr1, a1.formula, up2_I )
        val cl1 = ContractionLeftRule( andr1, a1.formula )
        val cut1 = CutRule( up1_nproof, cl1, a1.formula )
        val np = OrRightRule( cut1, up1_I, And( a1.formula, up2_I ) )

        val pp = OrLeftRule( up1_pproof, AndLeft2Rule( up2_pproof, a1.formula, up2_I ), up1_I, And( a1.formula, up2_I ) )

        ( np, pp, ipl )
      } else if ( ppart.contains( m ) ) {
        val ipl = Or( up1_I, And( a1F, up2_I ) )

        val andr1 = AndRightRule( Axiom( a1.formula ), up2_nproof, a1.formula, up2_I )
        val cut1 = CutRule( up1_nproof, andr1, a1.formula )
        val np = OrRightRule( cut1, up1_I, And( a1.formula, up2_I ) )

        val eqr1 = EquationRight1Rule( Axiom( a1.formula ), up2_pproof, a1.formula, a2.formula, m.formula )
        val andl1 = AndLeftRule( eqr1, a1.formula, up2_I )
        val pp = OrLeftRule( up1_pproof, andl1, up1_I, And( a1.formula, up2_I ) )

        ( np, pp, ipl )
      } else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case EquationRight2Rule( p1, p2, s, a1, a2, pos, m ) => {
      val a1F: FOLFormula = a1.formula.asInstanceOf[FOLFormula]
      val ( up1_nproof, up1_pproof, up1_I ) = applyUpEqualityLeft( p1, a1, npart, ppart, true )
      val ( up2_nproof, up2_pproof, up2_I ) = applyUpBinaryRight( p2, npart, ppart )

      if ( npart.contains( m ) ) {
        val ipl = Or( up1_I, And( a1F, up2_I ) )

        val eqr1 = EquationRight2Rule( Axiom( a1.formula ), up2_nproof, a1.formula, a2.formula, m.formula )
        val andr1 = AndRightRule( Axiom( a1.formula ), eqr1, a1.formula, up2_I )
        val cl1 = ContractionLeftRule( andr1, a1.formula )
        val cut1 = CutRule( up1_nproof, cl1, a1.formula )
        val np = OrRightRule( cut1, up1_I, And( a1.formula, up2_I ) )

        val pp = OrLeftRule( up1_pproof, AndLeft2Rule( up2_pproof, a1.formula, up2_I ), up1_I, And( a1.formula, up2_I ) )

        ( np, pp, ipl )
      } else if ( ppart.contains( m ) ) {
        val ipl = Or( up1_I, And( a1F, up2_I ) )

        val andr1 = AndRightRule( Axiom( a1.formula ), up2_nproof, a1.formula, up2_I )
        val cut1 = CutRule( up1_nproof, andr1, a1.formula )
        val np = OrRightRule( cut1, up1_I, And( a1.formula, up2_I ) )

        val eqr1 = EquationRight2Rule( Axiom( a1.formula ), up2_pproof, a1.formula, a2.formula, m.formula )
        val andl1 = AndLeftRule( eqr1, a1.formula, up2_I )
        val pp = OrLeftRule( up1_pproof, andl1, up1_I, And( a1.formula, up2_I ) )

        ( np, pp, ipl )
      } else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case EquationLeft1Rule( p1, p2, s, a1, a2, pos, m ) => {
      val a1F: FOLFormula = a1.formula.asInstanceOf[FOLFormula]
      val ( up1_nproof, up1_pproof, up1_I ) = applyUpEqualityLeft( p1, a1, npart, ppart, false )
      val ( up2_nproof, up2_pproof, up2_I ) = applyUpBinaryRight( p2, npart, ppart )

      if ( npart.contains( m ) ) {
        val ipl = And( up1_I, Imp( a1F, up2_I ) )

        val eql1 = EquationLeft1Rule( Axiom( a1.formula ), up2_nproof, a1.formula, a2.formula, m.formula )
        val impr1 = ImpRightRule( eql1, a1.formula, up2_I )
        val np = AndRightRule( up1_nproof, impr1, up1_I, Imp( a1.formula, up2_I ) )

        val impl1 = ImpLeftRule( Axiom( a1.formula ), up2_pproof, a1.formula, up2_I )
        val cut1 = CutRule( up1_pproof, impl1, a1.formula )
        val pp = AndLeftRule( cut1, up1_I, Imp( a1.formula, up2_I ) )

        ( np, pp, ipl )
      } else if ( ppart.contains( m ) ) {
        val ipl = And( up1_I, up2_I )

        val np = AndRightRule( up1_nproof, up2_nproof, up1_I, up2_I )

        val eql1 = EquationLeft1Rule( up1_pproof, up2_pproof, a1.formula, a2.formula, m.formula )
        val pp = AndLeftRule( eql1, up1_I, up2_I )

        ( np, pp, ipl )
      } else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case EquationLeft2Rule( p1, p2, s, a1, a2, pos, m ) => {
      val a1F: FOLFormula = a1.formula.asInstanceOf[FOLFormula]
      val ( up1_nproof, up1_pproof, up1_I ) = applyUpEqualityLeft( p1, a1, npart, ppart, false )
      val ( up2_nproof, up2_pproof, up2_I ) = applyUpBinaryRight( p2, npart, ppart )

      if ( npart.contains( m ) ) {
        val ipl = And( up1_I, Imp( a1F, up2_I ) )

        val eql1 = EquationLeft2Rule( Axiom( a1.formula ), up2_nproof, a1.formula, a2.formula, m.formula )
        val impr1 = ImpRightRule( eql1, a1.formula, up2_I )
        val np = AndRightRule( up1_nproof, impr1, up1_I, Imp( a1.formula, up2_I ) )

        val impl1 = ImpLeftRule( Axiom( a1.formula ), up2_pproof, a1.formula, up2_I )
        val cut1 = CutRule( up1_pproof, impl1, a1.formula )
        val pp = AndLeftRule( cut1, up1_I, Imp( a1.formula, up2_I ) )

        ( np, pp, ipl )
      } else if ( ppart.contains( m ) ) {
        val ipl = And( up1_I, up2_I )

        val np = AndRightRule( up1_nproof, up2_nproof, up1_I, up2_I )

        val eql1 = EquationLeft2Rule( up1_pproof, up2_pproof, a1.formula, a2.formula, m.formula )
        val pp = AndLeftRule( eql1, up1_I, up2_I )

        ( np, pp, ipl )
      } else throw new InterpolationException( "Negative and positive part must form a partition of the end-sequent." )
    }

    case _ => throw new InterpolationException( "Unknown inference rule of type: " + p.rule.toString() + "." )
  }

  private def applyUpUnary( p: LKProof, npart: Set[FormulaOccurrence], ppart: Set[FormulaOccurrence] ) = {
    val up_npart = npart.foldLeft( Set[FormulaOccurrence]() )( ( s, o ) => s ++ o.parents )
    val up_ppart = ppart.foldLeft( Set[FormulaOccurrence]() )( ( s, o ) => s ++ o.parents )
    apply( p, up_npart, up_ppart )
  }

  // TODO - is there a better way to get the ancestors of a set in the left or right subproof respectively?
  private def applyUpBinaryLeft( p1: LKProof, npart: Set[FormulaOccurrence], ppart: Set[FormulaOccurrence] ) = {
    val up_npart = npart.foldLeft( Set[FormulaOccurrence]() )( ( s, o ) => s ++ o.parents )
    val up_ppart = ppart.foldLeft( Set[FormulaOccurrence]() )( ( s, o ) => s ++ o.parents )
    val up1_npart = up_npart.filter( o => p1.root.antecedent.contains( o ) || p1.root.succedent.contains( o ) )
    val up1_ppart = up_ppart.filter( o => p1.root.antecedent.contains( o ) || p1.root.succedent.contains( o ) )

    apply( p1, up1_npart, up1_ppart )
  }

  private def applyUpBinaryRight( p2: LKProof, npart: Set[FormulaOccurrence], ppart: Set[FormulaOccurrence] ) = {
    val up_npart = npart.foldLeft( Set[FormulaOccurrence]() )( ( s, o ) => s ++ o.parents )
    val up_ppart = ppart.foldLeft( Set[FormulaOccurrence]() )( ( s, o ) => s ++ o.parents )
    val up2_npart = up_npart.filter( o => p2.root.antecedent.contains( o ) || p2.root.succedent.contains( o ) )
    val up2_ppart = up_ppart.filter( o => p2.root.antecedent.contains( o ) || p2.root.succedent.contains( o ) )

    apply( p2, up2_npart, up2_ppart )
  }

  private def applyUpEqualityLeft( p1: LKProof, a1: FormulaOccurrence, npart: Set[FormulaOccurrence], ppart: Set[FormulaOccurrence], isRightRule: Boolean ) = {
    val up_npart = npart.foldLeft( Set[FormulaOccurrence]() )( ( s, o ) => s ++ o.parents )
    val up_ppart = ppart.foldLeft( Set[FormulaOccurrence]() )( ( s, o ) => s ++ o.parents )
    var up1_npart = up_npart.filter( o => p1.root.antecedent.contains( o ) || p1.root.succedent.contains( o ) )
    var up1_ppart = up_ppart.filter( o => p1.root.antecedent.contains( o ) || p1.root.succedent.contains( o ) )

    // when dealing with EqualityRight (EqualityLeft), we always put the left auxiliary formula (i.e. the equality atom) into the left (right) partition
    if ( isRightRule ) {
      up1_npart += a1
      up1_ppart -= a1
    } else {
      up1_npart -= a1
      up1_ppart += a1
    }

    apply( p1, up1_npart, up1_ppart )
  }

  private def applyUpCutLeft( p1: LKProof, npart: Set[FormulaOccurrence], ppart: Set[FormulaOccurrence], a1: FormulaOccurrence ) = {
    val up_npart = npart.foldLeft( Set[FormulaOccurrence]() )( ( s, o ) => s ++ o.parents )
    val up_ppart = ppart.foldLeft( Set[FormulaOccurrence]() )( ( s, o ) => s ++ o.parents )
    var up1_npart = up_npart.filter( o => p1.root.antecedent.contains( o ) || p1.root.succedent.contains( o ) )
    var up1_ppart = up_ppart.filter( o => p1.root.antecedent.contains( o ) || p1.root.succedent.contains( o ) )

    val up_npartFold = up_npart.foldLeft( Seq[HOLFormula]() )( ( s, o ) => s :+ o.formula )
    val up_ppartFold = up_ppart.foldLeft( Seq[HOLFormula]() )( ( s, o ) => s :+ o.formula )

    if ( up_npartFold.contains( a1.formula ) && !up_ppartFold.contains( a1.formula ) ) {
      up1_npart += a1
    } else if ( up_ppartFold.contains( a1.formula ) && !up_npartFold.contains( a1.formula ) ) {
      up1_ppart += a1
    } else {
      up1_npart += a1
    }

    apply( p1, up1_npart, up1_ppart )
  }

  private def applyUpCutRight( p2: LKProof, s: OccSequent, npart: Set[FormulaOccurrence], ppart: Set[FormulaOccurrence], a2: FormulaOccurrence ) = {
    val up_npart = npart.foldLeft( Set[FormulaOccurrence]() )( ( s, o ) => s ++ o.parents )
    val up_ppart = ppart.foldLeft( Set[FormulaOccurrence]() )( ( s, o ) => s ++ o.parents )
    var up2_npart = up_npart.filter( o => p2.root.antecedent.contains( o ) || p2.root.succedent.contains( o ) )
    var up2_ppart = up_ppart.filter( o => p2.root.antecedent.contains( o ) || p2.root.succedent.contains( o ) )

    val up_npartFold = up_npart.foldLeft( Seq[HOLFormula]() )( ( s, o ) => s :+ o.formula )
    val up_ppartFold = up_ppart.foldLeft( Seq[HOLFormula]() )( ( s, o ) => s :+ o.formula )

    if ( up_npartFold.contains( a2.formula ) && !up_ppartFold.contains( a2.formula ) ) {
      up2_npart += a2
    } else if ( up_ppartFold.contains( a2.formula ) && !up_npartFold.contains( a2.formula ) ) {
      up2_ppart += a2
    } else {
      up2_npart += a2
    }

    apply( p2, up2_npart, up2_ppart )
  }

}

