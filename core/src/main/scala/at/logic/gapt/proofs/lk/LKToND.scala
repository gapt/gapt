package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Ant, Sequent, SequentIndex, Suc, lk, nd }
import at.logic.gapt.proofs.nd._

object LKToND {

  /**
   * Extracts an expansion sequent Ex(π) from an LKProof π.
   *
   * The induction rule is not supported!
   *
   * @param proof The proof π.
   * @return The natural deduction proof translate(π).
   */
  def apply( proof: LKProof ): NDProof = {
    translate( proof, Suc( 0 ) )
  }

  def apply( proof: LKProof, focus: SequentIndex ): NDProof = {
    translate( proof, focus )
  }

  private def exchange( subProof: NDProof, mainFormula: HOLFormula ): NDProof = {
    if ( mainFormula == subProof.endSequent( Suc( 0 ) ) ) {
      subProof
    } else {
      val negMain = hof"-$mainFormula"
      val p = if ( subProof.endSequent.antecedent.contains( negMain ) ) subProof else WeakeningRule( subProof, negMain )
      //val p = WeakeningRule( subProof, negMain )
      //val p = subProof

      val r = p.endSequent( Suc( 0 ) )

      val ax1 = nd.LogicalAxiom( mainFormula )

      val ax2 = nd.LogicalAxiom( hof"-$r" )
      val pr1 = NegElimRule( ax2, p )
      val pr2 = BottomElimRule( pr1, mainFormula )

      val i = pr2.endSequent.indexOfPolOption( negMain, Polarity.InAntecedent )
      ExcludedMiddleRule( ax1, Ant( 0 ), pr2, i.get )
    }
  }

  private def translate( proof: LKProof, focus: SequentIndex ): NDProof = proof match {

    // Axioms
    case lk.LogicalAxiom( atom: HOLAtom ) =>
      nd.LogicalAxiom( atom )

    case ReflexivityAxiom( s ) =>
      ???

    case TopAxiom =>
      ???

    case BottomAxiom =>
      ???

    case TheoryAxiom( sequent ) =>
      ???

    // Structural rules
    case WeakeningLeftRule( subProof, formula ) =>
      //translate( subProof, focus )
      WeakeningRule( translate( subProof, focus ), formula )

    case p @ WeakeningRightRule( subProof, formula ) =>
      //translate( subProof, focus )
      p.getSequentConnector.parentOption( focus ) match {
        case Some( i ) =>
          WeakeningRule( translate( subProof, i ), hof"-$formula" )
        case None =>
          //exchange( translate( subProof, Suc( 0 ) ), p.endSequent( focus ) )
          // different order as in other rules
          // explicit weakening here? would (exchange o translate) be enough?
          val t = translate( subProof, Suc( 0 ) )
          val ret = exchange( WeakeningRule( t, hof"-$formula" ), p.endSequent( focus ) )
          ret

        //without weakening weakenright/contractright example breaks
        //exchange( translate( subProof, Suc( 0 ) ), p.endSequent( focus ) )
      }

    case ContractionLeftRule( subProof, aux1, aux2 ) =>
      val l = subProof.endSequent( aux1 )
      val r = subProof.endSequent( aux2 )

      val t = translate( subProof, aux2 )

      assert( l == r )

      ContractionRule( t, l )

    case ContractionRightRule( subProof, aux1, aux2 ) =>
      val l = subProof.endSequent( aux1 )
      val r = subProof.endSequent( aux2 )

      val t = translate( subProof, aux2 )

      assert( l == r )

      val p1 = exchange( t, l )
      val il = p1.endSequent.find { case s if s == hof"-$l" => true; case _ => false }
      ExcludedMiddleRule( nd.LogicalAxiom( l ), Ant( 0 ), p1, il.get )

    case p @ CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val l = leftSubProof.endSequent( aux1 )

      val tl = p.getLeftSequentConnector.parentOption( aux1 ) match {
        case Some( i ) =>
          translate( leftSubProof, i )
        case None =>
          exchange( translate( leftSubProof, Suc( 0 ) ), l )
      }

      val tr = p.getRightSequentConnector.parentOption( focus ) match {
        case Some( i ) =>
          exchange( translate( rightSubProof, i ), p.endSequent( focus ) )
        case None =>
          exchange( translate( rightSubProof, Suc( 0 ) ), p.endSequent( focus ) )
      }

      ImpElimRule( ImpIntroRule( tl, hof"$l" ), tr )

    /*
      val tl = translate( leftSubProof, aux1 )
      val pl = exchange( tl, l )

      val ff = proof.endSequent( focus )
      val ir = rightSubProof.endSequent.find { case `ff` => true; case _ => false }
      val tr = ir match {
        case Some( ir ) if ir.isAnt => translate( rightSubProof, ir )
        case _                      => translate( rightSubProof, Ant( 0 ) )
      }
      val pr = exchange( tr, ff )

      val p1 = ImpIntroRule( pl, hof"$l" )
      ImpElimRule( p1, pr )
      */

    // Propositional rules
    case NegLeftRule( subProof, aux ) =>
      val r = subProof.endSequent( aux )
      val tr = translate( subProof, aux )

      val s = nd.LogicalAxiom( hof"-$r" )
      NegElimRule( s, tr )

    case p @ NegRightRule( subProof, aux ) =>
      val l = subProof.endSequent( aux )
      /*
      val t = exchange( translate( subProof, Ant( 0 ) ), Bottom() )
      */

      // exchanging with bottom in both cases
      val t = p.getSequentConnector.parentOption( focus ) match {
        case Some( i ) =>
          exchange( translate( subProof, i ), Bottom() )
        case None =>
          exchange( translate( subProof, Suc( 0 ) ), Bottom() )
      }

      NegIntroRule( t, l )

    case AndLeftRule( subProof, aux1, aux2 ) =>
      /*
      val l = subProof.endSequent( aux1 )
      val r = subProof.endSequent( aux2 )

      val ff = proof.endSequent( focus )

      val il = subProof.endSequent.find{ case `ff` => true; case _ => false }
      val t = translate( subProof, il.get )

      val l1 = exchange( t, ff )

      val r1 = LogicalAxiom( hof"$l & $r" )
      // TODO Elim1/Elim2 based on weakening in sub proof
      val r2 = AndElim1Rule
      */
      ???

    case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val l = leftSubProof.endSequent( aux1 )
      val r = rightSubProof.endSequent( aux2 )

      val tl = translate( leftSubProof, aux1 )
      val tr = translate( rightSubProof, aux2 )

      AndIntroRule( exchange( tl, l ), exchange( tr, r ) )

    case p @ OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>

      val tl = p.getLeftSequentConnector.parentOption( focus ) match {
        case Some( il ) =>
          translate( leftSubProof, il )
        case None =>
          // TODO pick new focus heuristically
          //exchange( translate( leftSubProof, Suc( 0 ) ), p.endSequent( focus ) )
          val t = WeakeningRule( translate( leftSubProof, Suc( 0 ) ), Neg( p.endSequent( focus ) ) )
          exchange( t, p.endSequent( focus ) )
      }

      val tr = p.getRightSequentConnector.parentOption( focus ) match {
        case Some( ir ) =>
          translate( rightSubProof, ir )
        case None =>
          // TODO pick new focus heuristically
          //exchange( translate( rightSubProof, Suc( 0 ) ), p.endSequent( focus ) )
          val t = WeakeningRule( translate( rightSubProof, Suc( 0 ) ), Neg( p.endSequent( focus ) ) )
          exchange( t, p.endSequent( focus ) )
      }

      OrElimRule( tl, tr, nd.LogicalAxiom( p.mainFormula ) )

    case p @ OrRightRule( subProof1 @ WeakeningRightRule( subProof2, f ), aux1, aux2 ) =>
      val l = subProof1.endSequent( aux1 )
      val r = subProof1.endSequent( aux2 )

      val ret = f match {
        case `r` =>
          val t = subProof1.getSequentConnector.parentOption( aux1 ) match {
            case Some( i ) =>
              translate( subProof2, i )
            case None =>
              exchange( translate( subProof2, Suc( 0 ) ), subProof2.endSequent( aux1 ) )
          }
          OrIntro1Rule( t, f )
        case `l` =>
          val t = subProof1.getSequentConnector.parentOption( aux2 ) match {
            case Some( i ) =>
              translate( subProof2, i )
            case None =>
              exchange( translate( subProof2, Suc( 0 ) ), subProof2.endSequent( aux2 ) )
          }
          OrIntro2Rule( t, f )
      }
      ret

    case p @ OrRightRule( subProof, aux1, aux2 ) =>
      val Or( l, r ) = p.mainFormula

      val t = translate( subProof, aux2 )
      val lp = OrIntro2Rule( exchange( t, r ), l )
      val rp1 = nd.LogicalAxiom( l )
      val rp2 = OrIntro1Rule( rp1, r )

      val i = lp.endSequent.indexOfPolOption( Neg( l ), Polarity.InAntecedent )
      ExcludedMiddleRule( rp2, Ant( 0 ), lp, i.get )

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val l = leftSubProof.endSequent( aux1 )
      val r = rightSubProof.endSequent( aux2 )

      val ff = proof.endSequent( focus )

      val tl = translate( leftSubProof, aux1 )

      val ir = rightSubProof.endSequent.find { case `ff` => true; case _ => false }
      val tr = ir match {
        case Some( ir ) if ir.isAnt => translate( rightSubProof, ir )
        case _                      => translate( rightSubProof, Ant( 0 ) )
      }

      val ax = nd.LogicalAxiom( hof"$l -> $r" )
      val tl2 = ImpElimRule( ax, exchange( tl, l ) )

      val er = exchange( tr, ff )
      val ir2 = er.endSequent.find { case `r` => true; case _ => false }
      val tr2 = ImpIntroRule( er, ir2.get )

      ImpElimRule( tr2, tl2 )

    case p @ ImpRightRule( subProof, aux1, aux2 ) =>
      val Imp( l, r ) = p.mainFormula

      val t = exchange( translate( subProof, aux2 ), r )

      val i = t.endSequent.indexOfPolOption( l, Polarity.InAntecedent )
      val ret = ImpIntroRule( t, i.get )
      ret

    // Quantifier rules
    case ForallLeftRule( subProof, aux, _, t, _ ) =>
      ???

    case ForallRightRule( subProof, aux, eigen, _ ) =>
      ???

    case ForallSkRightRule( subProof, aux, main, skT, skD ) =>
      ???

    case ExistsLeftRule( subProof, aux, eigen, _ ) =>
      ???

    case ExistsSkLeftRule( subProof, aux, main, skT, skD ) =>
      ???

    case ExistsRightRule( subProof, aux, _, t, _ ) =>
      ???

    // Equality rules
    case p: EqualityRule =>
      ???

    case DefinitionLeftRule( subProof, aux, main ) =>
      ???

    case DefinitionRightRule( subProof, aux, main ) =>
      ???
  }
}