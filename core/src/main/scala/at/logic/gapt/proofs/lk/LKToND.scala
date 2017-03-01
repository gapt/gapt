package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{Ant, Sequent, SequentIndex, Suc, lk, nd}
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
    translate( proof, Suc(0) )
  }

  def apply( proof: LKProof, focus: SequentIndex ): NDProof = {
    translate( proof, focus )
  }

  private def exchange( subProof: NDProof, mainFormula: HOLFormula  ): NDProof = {
    if (mainFormula == subProof.endSequent(Suc(0))) {
      subProof
    } else {
      val il = subProof.endSequent.find { case s if s == hof"-$mainFormula" => true; case _ => false }
      val p = il match {
        case Some(_) =>
          subProof
        case None =>
          WeakeningRule(subProof, hof"-$mainFormula")
      }

      val r = p.endSequent(Suc(0))

      val notRt = nd.LogicalAxiom(hof"-$r")

      val rt = nd.LogicalAxiom(hof"$mainFormula")

      val s1 = NegElimRule(notRt, p)
      val s2 = BottomElimRule(s1, mainFormula)
      val i = s2.endSequent.find { case s if s == hof"-$mainFormula" => true; case _ => false }.get

      ExcludedMiddleRule(rt, Ant(0), s2, i)
    }
  }


  private def translate( proof: LKProof, focus: SequentIndex ): NDProof = proof match {

    // Axioms
    case lk.LogicalAxiom( atom: HOLAtom ) =>
      nd.LogicalAxiom( atom )

    case ReflexivityAxiom( s )         =>
      ???

    case TopAxiom                      =>
      ???

    case BottomAxiom                   =>
      ???

    case TheoryAxiom( sequent )        =>
      ???

    // Structural rules
    case WeakeningLeftRule( subProof, formula ) =>
      val p = translate(subProof, focus)
      WeakeningRule( p, hof"$formula" )

    case WeakeningRightRule( subProof, formula ) =>
      val p = translate(subProof, focus)
      WeakeningRule( p, hof"-$formula" )

    case ContractionLeftRule( subProof, aux1, aux2 ) =>
      val l = subProof.endSequent(aux1)
      val r = subProof.endSequent(aux2)

      val t = translate(subProof, aux2)

      assert (l == r)

      ContractionRule(t, l)

    case ContractionRightRule( subProof, aux1, aux2 ) =>
      ???

    case c @ CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      ???

    // Propositional rules
    case NegLeftRule( subProof, aux ) =>
      val r = subProof.endSequent(aux)

      val tr = translate(subProof, aux)

      val s = nd.LogicalAxiom( hof"-$r" )
      NegElimRule( s, tr )

    case NegRightRule( subProof, aux ) =>
      val l = subProof.endSequent(aux)

      val tl = translate(subProof, Ant(0))

      // TODO: move left instead of exchange?
      //NegIntroRule(exchange(tl, l), l)
      NegIntroRule(tl, l)

    case AndLeftRule( subProof, aux1, aux2 ) =>
      ???

    case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val l = leftSubProof.endSequent(aux1)
      val r = rightSubProof.endSequent(aux2)

      val tl = translate(leftSubProof, aux1)
      val tr = translate(rightSubProof, aux2)

      AndIntroRule(exchange(tl, l), exchange(tr, r))


    case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val l = leftSubProof.endSequent( aux1 )
      val r = rightSubProof.endSequent( aux2 )

      val ff = proof.endSequent( focus )

      val il = leftSubProof.endSequent.find{ case `ff` => true; case _ => false }
      val tl = translate( leftSubProof, il.get )

      val ir = rightSubProof.endSequent.find{ case `ff` => true; case _ => false }
      val tr = translate( rightSubProof, ir.get )

      OrElimRule( exchange( tl, ff ), exchange( tr, ff ), nd.LogicalAxiom( hof"$l | $r" ) )


    case OrRightRule( subProof1 @ WeakeningRightRule(subProof2, f), aux1, aux2 ) =>
      val l = subProof1.endSequent(aux1)
      val r = subProof1.endSequent(aux2)

      // TODO pick logically simpler one?
      val t = translate(subProof2, aux2)
      f match {
        case `l` =>
          OrIntro2Rule(t, f)
        case `r` =>
          OrIntro1Rule(t, f)
      }

    case OrRightRule( subProof, aux1, aux2 ) =>
      val l = subProof.endSequent(aux1)
      val r = subProof.endSequent(aux2)

      // TODO pick logically simpler one?
      val ff = subProof.endSequent( aux2 )

      val t = translate(subProof, aux2)

      val lp = OrIntro2Rule( exchange( t, ff ), l)
      val rp1 = nd.LogicalAxiom(l)
      val rp2 = OrIntro1Rule(rp1, r)

      val il = lp.endSequent.find{ case s if s == hof"-$l" => true; case _ => false }
      ExcludedMiddleRule(rp2, Ant(0), lp, il.get)

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      ???

    case ImpRightRule( subProof, aux1, aux2 ) =>
      val l: HOLFormula = subProof.endSequent( aux1 )
      val r: HOLFormula = subProof.endSequent( aux2 )
      val t = translate( subProof, aux2 )
      val il = t.endSequent.find{ case `l` => true; case _ => false }
      ImpIntroRule( exchange( t, r ), il.get )

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