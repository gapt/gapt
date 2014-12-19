
package at.logic.algorithms.interpolation

import at.logic.language.hol._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk._
import at.logic.calculi.occurrences._

class InterpolationException(msg: String) extends Exception(msg)

object ExtractInterpolant {
  def apply( p: LKProof, npart: Set[FormulaOccurrence], ppart: Set[FormulaOccurrence] ) = Interpolate( p, npart, ppart )._3
}

object Interpolate
{
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
   *              a proof of I, \Pi |- \Lambda, the HOLFormula I )
   * @throws InterpolationException if the input proof is not propositional
   *         and cut-free or if (npart,ppart) is not a partition of its
   *         end-sequent.
   */
  def apply( p: LKProof, npart: Set[FormulaOccurrence], ppart: Set[FormulaOccurrence] ): ( LKProof, LKProof, HOLFormula ) = p match {

    case Axiom( s ) => {
      // we assume here that s has exactly one formula in the antecedent and exactly one in the succedent
      //            and that these two formulas are identical
      val oant = s.antecedent(0)
      val osuc = s.succedent(0)
      val form = oant.formula

      if      ( npart.contains( oant ) && npart.contains( osuc ) )  ( WeakeningRightRule( p, BottomC ), Axiom( BottomC::Nil, Nil ), BottomC )
      else if ( npart.contains( oant ) && ppart.contains( osuc ) )  ( p, p, form )
      else if ( ppart.contains( oant ) && npart.contains( osuc ) )  ( NegRightRule( p, form ), NegLeftRule( p, form ), Neg( form ) )
      else if ( ppart.contains( oant ) && ppart.contains( osuc ) )  ( Axiom( Nil, TopC::Nil ), WeakeningLeftRule( p, TopC ), TopC )
      else throw new InterpolationException( "Negative part and positive part must form a partition of the end-sequent." )
    }

    // structural rules

    case WeakeningLeftRule( p, s, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      if      ( npart.contains( m ) )  ( WeakeningLeftRule( up_nproof, m.formula ), up_pproof, up_I )
      else if ( ppart.contains( m ) )  ( up_nproof, WeakeningLeftRule( up_pproof, m.formula ), up_I )
      else throw new InterpolationException( "Negative part and positive part must form a partition of the end-sequent." )
    }

    case WeakeningRightRule( p, s, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      if      ( npart.contains( m ) )  ( WeakeningRightRule( up_nproof, m.formula ), up_pproof, up_I )
      else if ( ppart.contains( m ) )  ( up_nproof, WeakeningRightRule( up_pproof, m.formula ), up_I )
      else throw new InterpolationException( "Negative part and positive part must form a partition of the end-sequent." )
    }

    case ContractionLeftRule( p, s, a1, a2, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      if      ( npart.contains( m ) )  ( ContractionLeftRule( up_nproof, m.formula ), up_pproof, up_I )
      else if ( ppart.contains( m ) )  ( up_nproof, ContractionLeftRule( up_pproof, m.formula ), up_I )
      else throw new InterpolationException( "Negative part and positive part must form a partition of the end-sequent." )
    }

    case ContractionRightRule( p, s, a1, a2, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      if      ( npart.contains( m ) )  ( ContractionRightRule( up_nproof, m.formula ), up_pproof, up_I )
      else if ( ppart.contains( m ) )  ( up_nproof, ContractionRightRule( up_pproof, m.formula ), up_I )
      else throw new InterpolationException( "Negative part and positive part must form a partition of the end-sequent." )
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
      }
      else if ( ppart.contains( m ) ) {
        val ipl = And( up1_I, up2_I )
        val np = AndRightRule( up1_nproof, up2_nproof, up1_I, up2_I )
        val pp = AndLeftRule( AndRightRule( up1_pproof, up2_pproof, a1.formula, a2.formula ), up1_I, up2_I )

        ( np, pp, ipl )
      }
      else throw new InterpolationException( "Negative part and positive part must form a partition of the end-sequent." )
    }

    case AndLeft1Rule( p, s, a, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      m.formula match { case And( l, r ) => // TODO - is this possible in a less ugly way, i.e. without matching? -- analogously below
        if ( npart.contains( m ) )       ( AndLeft1Rule( up_nproof, l, r ), up_pproof, up_I )
        else if ( ppart.contains( m ) )  ( up_nproof, AndLeft1Rule( up_pproof, l, r ), up_I )
        else throw new InterpolationException( "Negative part and positive part must form a partition of the end-sequent." )
      }
    }

    case AndLeft2Rule( p, s, a, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      m.formula match { case And( l, r ) =>
        if ( npart.contains( m ) )       ( AndLeft2Rule( up_nproof, l, r ), up_pproof, up_I )
        else if ( ppart.contains( m ) )  ( up_nproof, AndLeft2Rule( up_pproof, l, r ), up_I )
        else throw new InterpolationException( "Negative part and positive part must form a partition of the end-sequent." )
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
      }
      else if ( ppart.contains( m ) ) {
        val ipl = And( up1_I, up2_I )
        val np = AndRightRule( up1_nproof, up2_nproof, up1_I, up2_I )
        val pp = AndLeftRule( OrLeftRule( up1_pproof, up2_pproof, a1.formula, a2.formula ), up1_I, up2_I )

        ( np, pp, ipl )
      }
      else throw new InterpolationException( "Negative part and positive part must form a partition of the end-sequent." )
    }

    case OrRight1Rule( p, s, a, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      m.formula match { case Or( l, r ) =>
        if      ( npart.contains( m ) )  ( OrRight1Rule( up_nproof, l, r ), up_pproof, up_I )
        else if ( ppart.contains( m ) )  ( up_nproof, OrRight1Rule( up_pproof, l, r ), up_I )
        else throw new InterpolationException( "Negative part and positive part must form a partition of the end-sequent." )
      }
    }

    case OrRight2Rule( p, s, a, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      m.formula match { case Or( l, r ) =>
        if      ( npart.contains( m ) )  ( OrRight2Rule( up_nproof, l, r ), up_pproof, up_I )
        else if ( ppart.contains( m ) )  ( up_nproof, OrRight2Rule( up_pproof, l, r ), up_I )
        else throw new InterpolationException( "Negative part and positive part must form a partition of the end-sequent." )
      }
    }

    case NegLeftRule( p, s, a, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      if ( npart.contains( m ) )       ( NegLeftRule( up_nproof, a.formula ), up_pproof, up_I )
      else if ( ppart.contains( m ) )  ( up_nproof, NegLeftRule( up_pproof, a.formula ), up_I )
      else throw new InterpolationException( "Negative part and positive part must form a partition of the end-sequent." )
    }

    case NegRightRule( p, s, a, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      if ( npart.contains( m ) )       ( NegRightRule( up_nproof, a.formula ), up_pproof, up_I )
      else if ( ppart.contains( m ) )  ( up_nproof, NegRightRule( up_pproof, a.formula ), up_I )
      else throw new InterpolationException( "Negative part and positive part must form a partition of the end-sequent." )
    }

    case ImpLeftRule( p1, p2, s, a1, a2, m ) => {
      val ( up1_nproof, up1_pproof, up1_I ) = applyUpBinaryLeft( p1, npart, ppart )
      val ( up2_nproof, up2_pproof, up2_I ) = applyUpBinaryRight( p2, npart, ppart )

      if ( npart.contains( m ) ) {
        val ipl = Or( up1_I, up2_I )
        val np = OrRightRule( ImpLeftRule( up1_nproof, up2_nproof, a1.formula, a2.formula ), up1_I, up2_I )
        val pp = OrLeftRule( up1_pproof, up2_pproof, up1_I, up2_I )

        ( np, pp, ipl )
      }
      else if ( ppart.contains( m ) ) {
        val ipl = And( up1_I, up2_I )
        val np = AndRightRule( up1_nproof, up2_nproof, up1_I, up2_I )
        val pp = AndLeftRule( ImpLeftRule( up1_pproof, up2_pproof, a1.formula, a2.formula ), up1_I, up2_I )

        ( np, pp, ipl )
      }
      else throw new InterpolationException( "Negative part and positive part must form a partition of the end-sequent." )
    }

    case ImpRightRule( p, s, a1, a2, m ) => {
      val ( up_nproof, up_pproof, up_I ) = applyUpUnary( p, npart, ppart )

      if      ( npart.contains( m ) )  ( ImpRightRule( up_nproof, a1.formula, a2.formula ), up_pproof, up_I )
      else if ( ppart.contains( m ) )  ( up_nproof, ImpRightRule( up_pproof, a1.formula, a2.formula ), up_I )
      else throw new InterpolationException( "Negative part and positive part must form a partition of the end-sequent." )
    }

    case _ => throw new InterpolationException( "Unknown inference rule." )
  }

  private def applyUpUnary( p: LKProof, npart: Set[FormulaOccurrence], ppart: Set[FormulaOccurrence] ) = {
    val up_npart = npart.foldLeft(Set[FormulaOccurrence]())( (s, o) => s ++ o.parents )
    val up_ppart = ppart.foldLeft(Set[FormulaOccurrence]())( (s, o) => s ++ o.parents )
    apply( p, up_npart, up_ppart )
  }

  // TODO - is there a better way to get the ancestors of a set in the left or right subproof respectively?
  private def applyUpBinaryLeft( p1: LKProof, npart: Set[FormulaOccurrence], ppart: Set[FormulaOccurrence] ) = {
      val up_npart = npart.foldLeft(Set[FormulaOccurrence]())( (s, o) => s ++ o.parents )
      val up_ppart = ppart.foldLeft(Set[FormulaOccurrence]())( (s, o) => s ++ o.parents )
      val up1_npart = up_npart.filter( o => p1.root.antecedent.contains( o ) || p1.root.succedent.contains( o ) )
      val up1_ppart = up_ppart.filter( o => p1.root.antecedent.contains( o ) || p1.root.succedent.contains( o ) )

      apply( p1, up1_npart, up1_ppart )
  }

  private def applyUpBinaryRight( p2: LKProof, npart: Set[FormulaOccurrence], ppart: Set[FormulaOccurrence] ) = {
      val up_npart = npart.foldLeft(Set[FormulaOccurrence]())( (s, o) => s ++ o.parents )
      val up_ppart = ppart.foldLeft(Set[FormulaOccurrence]())( (s, o) => s ++ o.parents )
      val up2_npart = up_npart.filter( o => p2.root.antecedent.contains( o ) || p2.root.succedent.contains( o ) )
      val up2_ppart = up_ppart.filter( o => p2.root.antecedent.contains( o ) || p2.root.succedent.contains( o ) )

      apply( p2, up2_npart, up2_ppart )
  }

}

