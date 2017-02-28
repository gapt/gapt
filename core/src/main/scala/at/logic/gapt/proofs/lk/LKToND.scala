package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.{Ant, Context, Sequent, SequentIndex, Suc, nd}
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
    translate(proof, Suc(0))
  }

  private def exchange( subProof: NDProof, left: SequentIndex, right: SequentIndex ): NDProof = {
    val (l, _) = subProof.endSequent.focus(left)
    val (r, _) = subProof.endSequent.focus(right)


    val notRt = nd.LogicalAxiom( hof"-${r}" )

    val Neg(strip) = l
    val rt = nd.LogicalAxiom( hof"${strip}" )

    //println("notRt")
    //println(notRt)
    //println("subProof")
    //println(subProof)
    val s1 = NegElimRule( notRt, subProof )
    val s2 = BottomElimRule( s1, strip )
    //println("s2")
    //println(s2)
    val i = s2.endSequent.find{ case `l` => true; case _ => false }.get

    //println (i)
    //println (rt)
    val ret = ExcludedMiddleRule( rt, Ant( 0 ), s2, i )

    //println("ret")
    //println(ret)
    ret
  }

  private def applyRule(in: NDProof, l: HOLFormula, il: Option[SequentIndex], r: HOLFormula, ir: Option[SequentIndex], rule: (NDProof, SequentIndex)=> NDProof ) = {
    (il, ir) match {
      case (Some(il), Some(ir)) if il.isAnt && ir.isSuc =>
        rule(in, il)
      case _ =>
        val ir = in.endSequent.find{ case s if s == hof"-${r}" => true; case _ => false }
        val (p, j) = ir match {
          case Some(ir) => (in, ir)
          case None => (WeakeningRule(in, hof"-${r}"), Ant(0))
        }
        val s = exchange(p, j, Suc( 0 ) )

        val il = s.endSequent.find{ case `l` => true; case _ => false }
        val (p2, i) = il match {
          case Some(il) => (s, il)
          case None => (WeakeningRule(s, l), Ant(0))
        }
        rule(p2, i)
    }
  }

  // TODO what if -l is on RHS? Need to exchange? for NegL, the rule would just duplicate -l anyhow
  private def applyRule2(in: NDProof, l: HOLFormula, il: Option[SequentIndex], rule: (NDProof, SequentIndex)=> NDProof ) = {
    il match {
      case Some(il) if il.isAnt =>
        rule(in, il)
      case _ =>
        val p = WeakeningRule(in, l)
        rule(p, Ant(0))
    }
  }

  private def applyRule3(in: NDProof, r: HOLFormula, ir: Option[SequentIndex], rule: (NDProof, SequentIndex)=> NDProof ) = {
    ir match {
      case Some(ir) if ir.isSuc =>
        rule(in, Ant(0))
      case _ =>
        val ir = in.endSequent.find{ case s if s == hof"-${r}" => true; case _ => false }
        val (p, j) = ir match {
          case Some(ir) => (in, ir)
          case None => (WeakeningRule(in, hof"-${r}"), Ant(0))
        }
        val s = exchange(p, j, Suc( 0 ) )

        rule(s, Ant(0))
    }
  }

  private def applyBinaryRule(inl: NDProof, l: HOLFormula, il: Option[SequentIndex], inr: NDProof, r: HOLFormula, ir: Option[SequentIndex], rule: (NDProof, SequentIndex, NDProof, SequentIndex) => NDProof ) = {
    (il, ir) match {
      case (Some(il), Some(ir)) if il.isSuc && ir.isSuc =>
        rule(inl, il, inr, ir)
      case _ =>
        val ir = inr.endSequent.find{ case s if s == hof"-${r}" => true; case _ => false }
        val (p, j) = ir match {
          case Some(ir) => (inr, ir)
          case None => (WeakeningRule(inr, hof"-${r}"), Ant(0))
        }
        val s = exchange(p, j, Suc( 0 ) )

        val il = inl.endSequent.find{ case s if s == hof"-${l}" => true; case _ => false }
        val (p2, i) = il match {
          case Some(il) => (inl, il)
          case None => (WeakeningRule(inl, l), Ant(0))
        }
        val s2 = exchange(p2, i, Suc( 0 ) )
        rule(s, j, s2, i)
    }
  }

  private def translate( proof: LKProof, focus: SequentIndex ): NDProof = proof match {

    // Axioms
    case LogicalAxiom( atom: HOLAtom ) =>
      val ret = nd.LogicalAxiom( atom )
      //println(proof.name)
      //println( ret )

      ret

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
      translate(subProof, focus)

    case WeakeningRightRule( subProof, formula ) =>
      translate(subProof, focus)

    case ContractionLeftRule( subProof, aux1, aux2 ) =>
      val (l, s1): (HOLFormula, Sequent[HOLFormula]) = subProof.endSequent.focus(aux1)
      val (r, s2): (HOLFormula, Sequent[HOLFormula]) = subProof.endSequent.focus(aux2)

      val t = translate(subProof, aux2)

      assert (l == r)

      ContractionRule(t, l)

    case ContractionRightRule( subProof, aux1, aux2 ) =>
      ???

    case c @ CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      ???

    // Propositional rules
    case NegLeftRule( subProof, aux ) =>
      val (r, s1): (HOLFormula, Sequent[HOLFormula]) = subProof.endSequent.focus(aux)

      val tr = translate(subProof, aux)

      val ir = tr.endSequent.find{ case `r` => true; case _ => false }

      def rule (in: NDProof, ir: SequentIndex) = {
        val s = nd.LogicalAxiom( hof"-${r}" )
        NegElimRule( s, in )
      }

      applyRule3( tr, r, ir, rule )

    case NegRightRule( subProof, aux ) =>
      val (l, s1): (HOLFormula, Sequent[HOLFormula]) = subProof.endSequent.focus(aux)

      val tl = translate(subProof, aux)

      val il = tl.endSequent.find{ case `l` => true; case _ => false }

      def rule (in: NDProof, il: SequentIndex) = {
        NegIntroRule(in, il)
      }

      applyRule2(tl, l, il, rule)

    case AndLeftRule( subProof, aux1, aux2 ) =>
      ???

    case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>

      val (l, s1): (HOLFormula, Sequent[HOLFormula]) = leftSubProof.endSequent.focus(aux1)
      val (r, s2): (HOLFormula, Sequent[HOLFormula]) = rightSubProof.endSequent.focus(aux2)

      val tl = translate(leftSubProof, aux1)
      val tr = translate(rightSubProof, aux2)

      val il = tl.endSequent.find{ case `l` => true; case _ => false }
      val ir = tr.endSequent.find{ case `r` => true; case _ => false }

      def rule (inl: NDProof, il: SequentIndex, inr: NDProof, ir: SequentIndex) = {
        AndIntroRule(inl, inr)
      }

      applyBinaryRule(tl, l, il, tr, r, ir, rule)

    case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      ???

    case OrRightRule( sp1 @ WeakeningRightRule(sp2, f), aux1, aux2 ) =>
      val (l, s1): (HOLFormula, Sequent[HOLFormula]) = sp1.endSequent.focus(aux1)
      val (r, s2): (HOLFormula, Sequent[HOLFormula]) = sp1.endSequent.focus(aux2)

      //TODO remove focus argument
      val t = translate(sp2, aux1)
      f match {
        case `l` =>
          OrIntro2Rule(t, f)
        case `r` =>
          OrIntro1Rule(t, f)
      }

    case OrRightRule( subProof, aux1, aux2 ) =>

      val (l, s1): (HOLFormula, Sequent[HOLFormula]) = subProof.endSequent.focus(aux1)
      val (r, s2): (HOLFormula, Sequent[HOLFormula]) = subProof.endSequent.focus(aux2)

      val t = translate(subProof, aux2)

      println(t)

      val il = t.endSequent.find{ case s if s == hof"-${l}" => true; case _ => false }
      val ir = t.endSequent.find{ case `r` => true; case _ => false }

      def rule (in: NDProof, il: SequentIndex) = {

        println("in")
        println(in)
        val lp = OrIntro2Rule(in, l)
        val rp1 = nd.LogicalAxiom(l)
        val rp2 = OrIntro1Rule(rp1, r)
        ExcludedMiddleRule(rp2, Ant(0), lp, il)
      }

      applyRule(t, Neg(l), il, r, ir, rule)

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      ???

    case ImpRightRule( subProof, aux1, aux2 ) =>

      val (l, s1): (HOLFormula, Sequent[HOLFormula]) = subProof.endSequent.focus(aux1)
      val (r, s2): (HOLFormula, Sequent[HOLFormula]) = subProof.endSequent.focus(aux2)

      val t = translate(subProof, aux2)

      val il = t.endSequent.find{ case `l` => true; case _ => false }
      val ir = t.endSequent.find{ case `r` => true; case _ => false }

      def rule (in: NDProof, il: SequentIndex) = {
        ImpIntroRule(in, il)
      }

      applyRule(t, l, il, r, ir, rule)


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