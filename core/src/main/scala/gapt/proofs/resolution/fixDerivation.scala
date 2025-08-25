package gapt.proofs.resolution

import gapt.expr._
import gapt.expr.formula.Atom
import gapt.expr.formula.Eq
import gapt.expr.subst.Substitution
import gapt.expr.util.constants
import gapt.expr.util.freeVariables
import gapt.expr.util.rename
import gapt.logic.clauseSubsumption
import gapt.logic.hol.CNFn
import gapt.proofs._
import gapt.provers.escargot.{Escargot, NonSplittingEscargot}
import gapt.provers.{ResolutionProver, groundFreeVariables}

import scala.collection.immutable.HashMap

/**
 *  Sometimes, we have a resolution refutation R of a set of clauses C
 *  and want a refutation R' of a set C' such that C implies C'.
 *
 *  This algorithm tries to obtain R' by trying to replace clauses c
 *  from C in R by derivations of C from C'.
 *
 *  In general, if R is a derivation of a clause c, the result R' of fixDerivation(R)
 *  is a derivation of a subclause of c.
 */

object fixDerivation {
  def tryDeriveBySubsumptionModEq(to: HOLClause, from: HOLClause): Option[ResolutionProof] = scala.util.boundary {
    for (s <- clauseSubsumption.modEqSymm(from, to)) yield {
      var p = Factor(Subst(Input(from), s))

      val needToFlip =
        for ((a, i) <- p.conclusion.zipWithIndex) yield a match {
          case _ if to.contains(a, i.polarity)               => false
          case Eq(t, s) if to.contains(Eq(s, t), i.polarity) => true
          case _                                             => scala.util.boundary.break(None)
        }

      for (case ((a, true), i) <- p.conclusion zip needToFlip zipWithIndex)
        p = Flip(p, p.conclusion.indexOf(a, i.polarity))

      p = Factor(p)
      p
    }
  }

  def tryDeriveTrivial(to: HOLClause, from: Seq[HOLClause]) = to match {
    case _ if from contains to                       => Some(Input(to))
    case HOLClause(Seq(), Seq(Eq(t, t_))) if t == t_ => Some(Refl(t))
    case HOLClause(Seq(a), Seq(a_)) if a == a_       => Some(Taut(a))
    case _                                           => None
  }

  def tryDeriveViaResolution(to: HOLClause, from: Seq[HOLClause]) =
    findDerivationViaResolution(to, from.toSet, Escargot)

  private def findFirstSome[A, B](seq: Seq[A])(f: A => Option[B]): Option[B] =
    seq.view.flatMap(f(_)).headOption

  def apply(p: ResolutionProof, cs: Iterable[ResolutionProof]): ResolutionProof = {
    val csMap = cs.view.map(c => c.conclusion -> c).toMap
    mapInputClauses(apply(p, csMap.keySet.map(_.map(_.asInstanceOf[Atom])).toSeq))(csMap)
  }

  def apply(p: ResolutionProof, cs: Seq[HOLClause]): ResolutionProof =
    mapInputClauses(p) { seq =>
      val cls = seq.map(_.asInstanceOf[Atom])
      tryDeriveTrivial(cls, cs).orElse(findFirstSome(cs)(tryDeriveBySubsumptionModEq(cls, _))).orElse(tryDeriveViaResolution(cls, cs)).getOrElse {
        throw new IllegalArgumentException(s"Could not derive $cls from\n${cs mkString "\n"}")
      }
    }

  def apply(p: ResolutionProof, endSequent: HOLSequent): ResolutionProof = {
    val cnf = structuralCNF(endSequent, structural = false)
    mapInputClauses(fixDerivation(p, cnf.map(_.conclusion.map(_.asInstanceOf[Atom])).toSeq))(cls => cnf.find(_.conclusion == cls).get)
  }
}

object tautologifyInitialUnitClauses {

  /**
   * Replace matching initial clauses by tautologies.
   *
   * If shouldTautologify is true for an initial unit clause +-a, then it is replaced by the tautology a:-a.  The
   * resulting resolution proof has the same structure as the original proof.
   */
  def apply(p: ResolutionProof, shouldTautologify: HOLSequent => Boolean): ResolutionProof =
    mapInputClauses(p) {
      case clause @ Sequent(Seq(), Seq(a)) if shouldTautologify(clause) =>
        Taut(a)
      case clause @ Sequent(Seq(a), Seq()) if shouldTautologify(clause) =>
        Taut(a)
      case clause => Input(clause)
    }
}

object findDerivationViaResolution {

  /**
   * Finds a resolution derivation of a clause from a set of clauses.
   *
   * The resulting resolution proof ends in a subclause of the specified clause a, and its initial clauses are either
   * from bs, tautologies, or reflexivity.
   *
   * @param a Consequence to prove.
   * @param bs Set of initial clauses for the resulting proof.
   * @param prover Prover to obtain a resolution refutation of the consequence bs |= a from.
   * @return Resolution proof ending in a subclause of a, or None if the prover couldn't prove the consequence.
   */
  def apply(a: HOLClause, bs: Set[_ <: HOLClause], prover: ResolutionProver = NonSplittingEscargot): Option[ResolutionProof] = {
    val grounding = groundFreeVariables.getGroundingMap(
      freeVariables(a),
      (a.formulas ++ bs.flatMap(_.formulas)).flatMap(constants.nonLogical(_)).toSet
    )

    val groundingSubst = grounding
    val negatedClausesA = a.map(groundingSubst(_)).map(_.asInstanceOf[Atom]).map(Clause() :+ _, _ +: Clause()).elements

    prover.getResolutionProof(bs ++ negatedClausesA) map { refutation =>
      val tautologified = tautologifyInitialUnitClauses(eliminateSplitting(refutation), negatedClausesA.toSet)

      val toUnusedVars = rename(grounding.domain, containedNames(tautologified))
      val nonOverbindingUnground = Substitution(grounding.map.map { case (v, c) => toUnusedVars(v) -> c }, grounding.typeMap)
      val derivation = TermReplacement.undoGrounding(tautologified, nonOverbindingUnground)
      val derivationInOrigVars = Subst(derivation, Substitution(toUnusedVars.map(_.swap)))

      simplifyResolutionProof(derivationInOrigVars)
    }
  }
}
