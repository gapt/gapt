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
      //translate(subProof, focus)
      val ret = WeakeningRule(translate(subProof, focus), formula)
      //println(proof.name)
      //println(ret)

      ret

    case WeakeningRightRule( subProof, formula ) =>
      //translate(subProof, focus)
      val ret = WeakeningRule(translate(subProof, focus), hof"-${formula}")
      //println(proof.name)
      //println(ret)

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
      //println(seq)
      println(proof.name)
      println ("subProof")
      println (subProof)

      val t = translate(subProof, aux2)

      println(proof.name)
      println ("t")
      println (t)
      println("proof")
      println(proof)
      println(s"focus: ${focus}")
      val ff = proof.endSequent(focus)
      println(s"ff: ${ff}")

      val lp = OrIntro2Rule(t, l)

      val rp1 = nd.LogicalAxiom( l )
      val rp2 = OrIntro1Rule( rp1, r )

      //println("lp")
      //println(lp)
      //println("rp2")
      //println(rp2)

      val ret = ExcludedMiddleRule(rp2, Ant(0), lp, Ant(0))
      //println(proof.name)
      //println( ret )

      ret

    case ImpLeftRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      ???

    case ImpRightRule( subProof, aux1, aux2 ) =>

      val (l, s1): (HOLFormula, Sequent[HOLFormula]) = subProof.endSequent.focus(aux1)
      val (r, s2): (HOLFormula, Sequent[HOLFormula]) = subProof.endSequent.focus(aux2)

      println(proof.name)
      println ("subProof")
      println (subProof)
      // TODO find correct formula
      // TODO possibly exchange
      val t = translate(subProof, aux2)
      println(proof.name)
      println ("t")
      println (t)

      println(s"focus: ${focus}")
      println("proof")
      println(proof)
      val ff = proof.endSequent(focus)
      println(s"ff: ${ff}")

      //println("proof")
      //println(proof)
      //println(s"t.endSequent = ${t.endSequent}")
      //println(s"l = ${l}")
      //println(s"r = ${r}")
      val il = t.endSequent.find{ case `l` => true; case _ => false }
      val ir = t.endSequent.find{ case `r` => true; case _ => false }

      val ret = (il, ir) match {
        case (Some(il), Some(ir)) if il.isAnt && ir.isSuc =>
          ImpIntroRule(t, il)
        case (Some(il), Some(ir)) if il.isAnt && !ir.isSuc =>
          val ir = t.endSequent.find{ case s if s == hof"-${r}" => true; case _ => false }
          val s = exchange(t, ir.get, Suc( 0 ) )
          val i = t.endSequent.find{ case `l` => true; case _ => false }
          ImpIntroRule(s, i.get)
        case (Some(il), Some(ir)) if !il.isAnt && !ir.isSuc =>
          val s = exchange(t, il, ir)
          val i = t.endSequent.find{ case `l` => true; case _ => false }
          ImpIntroRule(s, i.get)
        case (Some(il), Some(ir)) if !il.isAnt && ir.isSuc =>
          // I think this case cannot happen
          ???
        case (Some(il), None) if il.isAnt =>
          val ir = t.endSequent.find{ case s if s == hof"-${r}" => true; case _ => false }
          val s = exchange(t, ir.get, Suc( 0 ) )
          val i = t.endSequent.find{ case `l` => true; case _ => false }
          ImpIntroRule(s, i.get)
        case _ =>
          ???
      }

      //println(proof.name)
      //println( ret )

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