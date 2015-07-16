package at.logic.gapt.proofs.resolution.robinson

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.grammars._
import at.logic.gapt.proofs.expansionTrees.InstanceTermEncoding
import at.logic.gapt.proofs.lk.base.HOLSequent
import at.logic.gapt.proofs.resolution._

object extractRecSchemFromResProof {
  def apply(p: RobinsonResolutionProof): RecursionScheme = {
    val cnf = initialSequents(p)
    val endSequent = HOLSequent(cnf.map(_.toFormula).map(univclosure(_)).toSeq, Seq())
    val encoding = new InstanceTermEncoding(endSequent)
    val (axiomRules, rest) = getRules(p, clause =>
      encoding.encodeOption(clause.toFormula.asInstanceOf[FOLFormula] -> true))
    val axiom = FOLFunction("A")
    RecursionScheme(axiomRules.map(r => Rule(axiom, r)) ++ rest)
  }

  private val freshSymbols = Stream.from( 1 ).map( i => s"B$i" ).iterator
  private def mkFreshSymbol(): String = freshSymbols.next()

  def getRules(p: RobinsonResolutionProof, clauseTerm: HOLClause => Option[FOLTerm]): (Set[FOLTerm], Set[Rule]) = p match {
    case InitialClause( clause ) => clauseTerm(clause.toHOLClause).toSet -> Set()
    case Factor( clause, p1, List( occurrences ), subst ) =>
      val (axiomRules, rest) = getRules(p1, clauseTerm)
      axiomRules.map(subst.apply) -> rest
    case Variant( clause, p1, subst ) =>
      val (axiomRules, rest) = getRules(p1, clauseTerm)
      axiomRules.map(subst.apply) -> rest
    case Instance( clause, p1, subst ) =>
      val (axiomRules, rest) = getRules(p1, clauseTerm)
      axiomRules.map(subst.apply) -> rest
    case Resolution( clause, p1, p2, occ1, occ2, subst ) =>
      val (axiomRules1, rest1) = getRules(p1, clauseTerm)
      val (axiomRules2, rest2) = getRules(p2, clauseTerm)
      (axiomRules1 ++ axiomRules2).map(subst.apply) -> (rest1 ++ rest2)
    case Paramodulation( clause, p1, p2, occ1, occ2, main, subst ) =>
      val (axiomRules1, rest1) = getRules(p1, clauseTerm)
      val (axiomRules2, rest2) = getRules(p2, clauseTerm)
      (axiomRules1 ++ axiomRules2).map(subst.apply) -> (rest1 ++ rest2)
  }
}