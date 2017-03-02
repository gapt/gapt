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

      val ax1 = nd.LogicalAxiom(hof"$mainFormula")

      val ax2 = nd.LogicalAxiom(hof"-$r")
      val pr1 = NegElimRule(ax2, p)
      val pr2 = BottomElimRule(pr1, mainFormula)

      val i = pr2.endSequent.find { case s if s == hof"-$mainFormula" => true; case _ => false }.get
      ExcludedMiddleRule(ax1, Ant(0), pr2, i)
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
      val l = subProof.endSequent(aux1)
      val r = subProof.endSequent(aux2)

      val t = translate(subProof, aux2)

      assert (l == r)

      val p1 = exchange( t, l )
      val il = p1.endSequent.find{ case s if s == hof"-$l" => true; case _ => false }
      ExcludedMiddleRule( nd.LogicalAxiom( hof"$l" ), Ant( 0 ), p1, il.get )

    case c @ CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val l = leftSubProof.endSequent(aux1)

      val tl = translate( leftSubProof, aux1 )
      val pl = exchange( tl, l )

      val ff = proof.endSequent( focus )
      val ir = rightSubProof.endSequent.find{ case `ff` => true; case _ => false }
      val tr = ir match {
        case Some(ir) if ir.isAnt => translate( rightSubProof, ir )
        case _ => translate( rightSubProof, Ant(0) )
      }
      val pr = exchange( tr, ff )

      val p1 = ImpIntroRule( pl, hof"$l" )
      ImpElimRule( p1, pr )

    // Propositional rules
    case NegLeftRule( subProof, aux ) =>
      val r = subProof.endSequent(aux)

      val tr = translate(subProof, Ant(0))

      val s = nd.LogicalAxiom( hof"-$r" )
      NegElimRule( s, tr )

    case NegRightRule( subProof, aux ) =>
      val l = subProof.endSequent(aux)

      val tl = translate(subProof, Ant(0))

      NegIntroRule(exchange(tl, Bottom()), l)

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
      val tl = il match {
        case Some( il ) if il.isAnt => translate( leftSubProof, il )
        case _ => translate( leftSubProof, Ant(0) )
      }
      val ir = rightSubProof.endSequent.find{ case `ff` => true; case _ => false }
      val tr = ir match {
        case Some(ir) if ir.isAnt => translate(rightSubProof, ir)
        case _ => translate(rightSubProof, Ant(0))
      }

      // TODO: duplication of focused formula necessary?
      //val tl2 = WeakeningRule(tl, hof"-$ff")
      val tl2 = tl
      //val tr2 = WeakeningRule(tr, hof"-$ff")
      val tr2 = tr
      val el = exchange( tl2, ff )
      val er = exchange( tr2, ff )
      OrElimRule( el, er, nd.LogicalAxiom( hof"$l | $r" ) )


    case OrRightRule( subProof1 @ WeakeningRightRule(subProof2, f), aux1, aux2 ) =>
      val l = subProof1.endSequent(aux1)
      val r = subProof1.endSequent(aux2)

      val ret = f match {
        case `l` =>
          val t = translate(subProof2, aux1)
          val t1 = exchange( t, r )
          OrIntro2Rule(t1, f)
        case `r` =>
          val t = translate(subProof2, aux2)
          val t1 = exchange( t, l )
          OrIntro1Rule(t1, f)
      }
      ret

    case OrRightRule( subProof, aux1, aux2 ) =>
      val l = subProof.endSequent(aux1)
      val r = subProof.endSequent(aux2)

      val t = translate(subProof, aux2)

      val lp = OrIntro2Rule( exchange( t, r ), l)
      val rp1 = nd.LogicalAxiom(l)
      val rp2 = OrIntro1Rule(rp1, r)

      val il = lp.endSequent.find{ case s if s == hof"-$l" => true; case _ => false }
      ExcludedMiddleRule(rp2, Ant(0), lp, il.get)

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val l = leftSubProof.endSequent( aux1 )
      val r = rightSubProof.endSequent( aux2 )

      val ff = proof.endSequent( focus )

      val tl = translate( leftSubProof, aux1 )

      val ir = rightSubProof.endSequent.find{ case `ff` => true; case _ => false }
      val tr = ir match {
        case Some (ir) if ir.isAnt => translate( rightSubProof, ir )
        case _ => translate( rightSubProof, Ant(0) )
      }

      val ax = nd.LogicalAxiom( hof"$l -> $r" )
      val tl2 = ImpElimRule( ax, exchange(tl, l) )

      val er = exchange( tr, ff )
      val ir2 = er.endSequent.find{ case `r` => true; case _ => false }
      val tr2 = ImpIntroRule( er, ir2.get)

      ImpElimRule( tr2, tl2 )

    case ImpRightRule( subProof, aux1, aux2 ) =>
      val l: HOLFormula = subProof.endSequent( aux1 )
      val r: HOLFormula = subProof.endSequent( aux2 )
      val t = translate( subProof, aux2 )
      val e = exchange( t, r )
      val il = e.endSequent.find{ case `l` => true; case _ => false }
      val ret = ImpIntroRule( e, il.get )
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