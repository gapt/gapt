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
    translate(proof)
  }

  private def exchange( subProof: NDProof, left: SequentIndex, right: SequentIndex ): (NDProof, SequentIndex) = {
    val (l, _) = subProof.endSequent.focus(left)
    val (r, _) = subProof.endSequent.focus(right)

    val notA = nd.LogicalAxiom( hof"-${l}" )
    val notB = nd.LogicalAxiom( hof"-${r}" )

    println("notA")
    println(notA)
    println("notB")
    println(notB)
    println("subProof")
    println(subProof)
    val s1 = NegElimRule( subProof, notB )
    val s2 = BottomElimRule( s1, hof"-${l}" )
    val i = s2.endSequent.find{ case `l` => true; case _ => false }.get

    val ret = ExcludedMiddleRule( notA, Ant(0), s2, i )
    val j = ret.endSequent.find{ case `r` => true; case _ => false }.get
    (ret, j)
  }

  private def translate( proof: LKProof ): NDProof = proof match {

    // Axioms
    case LogicalAxiom( atom: HOLAtom ) =>
      val ret = nd.LogicalAxiom( atom )
      println(proof.name)
      println( ret )

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
      val ret = WeakeningRule(translate(subProof), formula)
      println(proof.name)
      println(ret)

      ret

    case WeakeningRightRule( subProof, formula ) =>
      val ret = WeakeningRule(translate(subProof), hof"-${formula}")
      println(proof.name)
      println(ret)

      ret

    case ContractionLeftRule( subProof, aux1, aux2 ) =>
      ???

    case ContractionRightRule( subProof, aux1, aux2 ) =>
      ???

    case c @ CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      ???

    // Propositional rules
    case NegLeftRule( subProof, aux ) =>
      ???

    case NegRightRule( subProof, aux ) =>
      ???

    case AndLeftRule( subProof, aux1, aux2 ) =>
      ???

    case AndRightRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      ???

    case OrLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      ???

    case OrRightRule( subProof, aux1, aux2 ) =>
      val (l, s1): (HOLFormula, Sequent[HOLFormula]) = subProof.endSequent.focus(aux1)
      val (r, s2): (HOLFormula, Sequent[HOLFormula]) = subProof.endSequent.focus(aux2)

      // TODO move Delta to LHS of sequent
      val seq = le"-${l}" +: s1
      println(seq)

      val lp = OrIntro1Rule(translate(subProof), l)

      val rp1 = nd.LogicalAxiom( l )
      val rp2 = OrIntro1Rule( rp1, r )

      val ret = ExcludedMiddleRule(lp, Ant(0), rp2, Ant(0))
      println(proof.name)
      println( ret )

      ret

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      ???

    case ImpRightRule( subProof, aux1, aux2 ) =>
      val (l, s1): (HOLFormula, Sequent[HOLFormula]) = subProof.endSequent.focus(aux1)
      val (r, s2): (HOLFormula, Sequent[HOLFormula]) = subProof.endSequent.focus(aux2)

      // TODO find correct formula
      // TODO possibly exchange
      val t = translate(subProof)

      println("proof")
      println(proof)
      println(s"t.endSequent = ${t.endSequent}")
      println(s"l = ${l}")
      println(s"r = ${r}")
      val il = t.endSequent.find{ case `l` => true; case _ => false }
      val ir = t.endSequent.find{ case `r` => true; case _ => false }

      val ret = (il, ir) match {
        case (Some(il), Some(ir)) if il.isAnt && ir.isSuc =>
          ImpIntroRule(t, il)
        case (Some(il), Some(ir)) if il.isAnt && !ir.isSuc =>
          val (s, i) = exchange(t, ir, Suc( 0 ))
          ImpIntroRule(s, i)
        case (Some(il), Some(ir)) if !il.isAnt && !ir.isSuc =>
          val (s, i) = exchange(t, il, ir)
          ImpIntroRule(s, i)
        case (Some(il), Some(ir)) if !il.isAnt && ir.isSuc =>
          // I think this case cannot happen
          ???
        case _ =>
          ???
      }

      println(proof.name)
      println( ret )

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