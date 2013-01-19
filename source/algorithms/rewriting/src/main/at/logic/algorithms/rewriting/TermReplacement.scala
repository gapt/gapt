package at.logic.algorithms.rewriting

import at.logic.language.lambda.typedLambdaCalculus.{Abs, App, Var, LambdaExpression}
import at.logic.calculi.lk.base.types.FSequent
import at.logic.language.hol.{HOLFormula, HOLExpression}
import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.resolution.robinson._
import collection.immutable
import at.logic.language.fol.{FOLExpression, FOLFormula}
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.language.lambda.substitutions.Substitution
import at.logic.calculi.resolution.instance.Instance
import scala.Some

/******* Term Replacement **********
   replaces all occurences of term "what" by term "by" in term "term" -- be careful with replacing variables,
   there is no scope checking

   usable on subclasses of lambda expressions, fsequents and resolution proofs
 */

object TermReplacement{
  import NameReplacement.find_matching

  def apply[T <: LambdaExpression](term : T, what : T, by : T) : T = {
    require(what.exptype == by.exptype)
    rename_term(what,by,term)
  }

  def apply[T <: LambdaExpression](term : T, p : immutable.Map[T,T]) : T = p.foldLeft(term)((t, x) => apply(x._1, x._2, t))

  def rename_fsequent[T <: HOLExpression](fs : FSequent, what : T, by :T  ) : FSequent =
    FSequent(fs.antecedent.map(apply(what,by,_).asInstanceOf[HOLFormula]),
             fs.succedent.map( apply(what,by,_).asInstanceOf[HOLFormula]))

  def rename_fsequent[T <: HOLExpression](fs : FSequent, p : immutable.Map[T,T]  ) : FSequent = {
    val m = p.asInstanceOf[Map[HOLExpression,HOLExpression]] // need to cast, maps are not covariant
    FSequent(fs.antecedent.map(apply(_,m).asInstanceOf[HOLFormula]),
      fs.succedent.map( apply(_,m).asInstanceOf[HOLFormula]))
  }


  def rename_term[T <: LambdaExpression](what : T, by : T, term : T) : T = {
    term match {
      case Var(s, t) =>
        if (what == term) by else term
      case App(s,t) =>
        val s_ = if (s == what) by else rename_term(what, by, s)
        val t_ = if (t == what) by else rename_term(what, by, t)
        what.factory.createApp(s_, t_).asInstanceOf[T]
      case Abs(x,t) =>
        val t_ = if (t == what) by else rename_term(what, by, t)
        what.factory.createAbs(x, t_).asInstanceOf[T]
    }
  }

  def holapply[T <: HOLExpression](term : HOLExpression, o: OccMap) : T =
    apply[HOLExpression](term,o.asInstanceOf[immutable.Map[HOLExpression,HOLExpression]]).asInstanceOf[T]
  def folapply[T <: FOLExpression](term : FOLExpression, o: OccMap) : T =
    apply[FOLExpression](term,o.asInstanceOf[immutable.Map[FOLExpression,FOLExpression]]).asInstanceOf[T]

  // map from sumbol name to pair of Arity and replacement symbol name
  type SymbolMap = immutable.Map[FOLExpression, FOLExpression]
  type OccMap = immutable.Map[FormulaOccurrence, FormulaOccurrence]
  type ProofMap = immutable.Map[RobinsonResolutionProof, (OccMap, RobinsonResolutionProof)]

  val emptySymbolMap = immutable.Map[FOLExpression, FOLExpression]()
  val emptyOccMap = immutable.Map[FormulaOccurrence, FormulaOccurrence]()
  val emptyProofMap = immutable.Map[RobinsonResolutionProof, (OccMap, RobinsonResolutionProof)]()

  def extendw_pmap(index: RobinsonResolutionProof, p:ProofMap, o : OccMap, i : RobinsonResolutionProof) = (p + ((index,(o,i))), o, i)
  def add_pmap(pmap : ProofMap, parent: RobinsonResolutionProof) : (ProofMap, OccMap, RobinsonResolutionProof) = { val x=pmap(parent); (pmap, x._1, x._2) }

  def rename_resproof(p : RobinsonResolutionProof,
                      irules : Set[RobinsonResolutionProof],
                      smap : SymbolMap) : (OccMap, RobinsonResolutionProof) =
    rename_resproof(p, irules, smap, emptyProofMap)._1(p)

  def rename_resproof(p : RobinsonResolutionProof,
                      irules : Set[RobinsonResolutionProof],
                      smap : SymbolMap,
                      pmap : ProofMap)  : (ProofMap, OccMap, RobinsonResolutionProof) = {
    if (pmap contains p) add_pmap(pmap,p) else
      p match {
        case InitialClause(clause) =>
          //rename literals
          //val negp : immutable.List[FOLFormula] = clause.negative.toList map ((fo : FormulaOccurrence) =>apply(fo.formula.asInstanceOf[FOLFormula], smap))
          //val posp : immutable.List[FOLFormula] = clause.positive.toList map ((fo : FormulaOccurrence) =>apply(fo.formula.asInstanceOf[FOLFormula], smap))
          val FSequent(fnegp, fposp) = rename_fsequent(clause.toFSequent, smap)
          val negp = fnegp.toList.asInstanceOf[List[FOLFormula]]
          val posp = fposp.toList.asInstanceOf[List[FOLFormula]]

          val inference = InitialClause(negp, posp)
          //create map form original iteral occs to renamed literal occs
          val negm : immutable.Map[FormulaOccurrence, FOLFormula] = immutable.Map[FormulaOccurrence, FOLFormula]() ++ (clause.negative zip negp)
          val posm : immutable.Map[FormulaOccurrence, FOLFormula] = immutable.Map[FormulaOccurrence, FOLFormula]() ++ (clause.positive zip posp)
          def nmatcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = negm(o) == t.formula
          def pmatcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = posm(o) == t.formula

          //println(negm ++ posm)
          //println(clause)
          //println(inference.root)
          val rsmap = find_matching(clause.negative.toList, inference.root.negative.toList, nmatcher) ++
            find_matching(clause.positive.toList, inference.root.positive.toList, pmatcher)

          extendw_pmap(p, pmap, rsmap, inference)


/*
        case Variant(clause, parent1, sub) =>
          val (rpmap, rmap, rparent1) = if (pmap contains parent1) add_pmap(pmap, parent1) else rename_resproof(parent1, irules, smap, pmap)
          val smap : Map[Var, FOLExpression] = sub.map map ((x:(Var, FOLExpression)) => (x._1, apply(x._2, smap)) )
          val nsub = Substitution(smap)
          var inference :RobinsonResolutionProof = Variant(rparent1, nsub)

          def matcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = {
            val anc_correspondences : immutable.Seq[FormulaOccurrence] = o.ancestors.map(rmap)
            t.formula == apply(o.formula, smap) &&
              anc_correspondences.diff(t.ancestors).isEmpty &&
              t.ancestors.diff(anc_correspondences).isEmpty
          }

          val rsmap = find_matching(clause.negative.toList, inference.root.negative.toList, matcher) ++
            find_matching(clause.positive.toList, inference.root.positive.toList, matcher)

          extendw_pmap(p, rpmap, rsmap, inference)


        case Factor(clause, parent1, aux, sub) =>
          val (rpmap, rmap, rparent1) = if (pmap contains parent1) add_pmap(pmap, parent1) else rename_resproof(parent1, irules, smap, pmap)
          val nsub = Substitution(sub.map map ((x:(Var, FOLExpression)) => (x._1, apply(x._2, smap)) ))
          var inference :RobinsonResolutionProof = aux match {
            case lit1 :: Nil =>
              Factor(rparent1, rmap(lit1.head), lit1.tail map rmap, nsub)
            case lit1::lit2::Nil =>
              Factor(rparent1, rmap(lit1.head), lit1.tail map rmap, rmap(lit2.head), lit2.tail map rmap, nsub)
            case _ => throw new Exception("Factor rule for "+p.root+" does not have one or two primary formulas! aux="+aux)
          }

          def matcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = {
            val anc_correspondences : immutable.Seq[FormulaOccurrence] = o.ancestors.map(rmap)
            t.formula == apply(o.formula, smap) &&
              anc_correspondences.diff(t.ancestors).isEmpty &&
              t.ancestors.diff(anc_correspondences).isEmpty
          }

          val rsmap = find_matching(clause.negative.toList, inference.root.negative.toList, matcher) ++
            find_matching(clause.positive.toList, inference.root.positive.toList, matcher)

          extendw_pmap(p, rpmap, rsmap, inference)

        case Instance(clause, parent1, sub) =>
          val (rpmap, rmap, rparent1) = if (pmap contains parent1) add_pmap(pmap, parent1) else rename_resproof(parent1, irules, smap, pmap)
          val nsub = Substitution(sub.map map ((x:(Var, FOLExpression)) => (x._1, apply(x._2, smap)) ))
          var inference :RobinsonResolutionProof =  Instance(rparent1, nsub)

          def matcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = {
            val anc_correspondences : immutable.Seq[FormulaOccurrence] = o.ancestors.map(rmap)
            t.formula == apply(o.formula, smap) &&
              anc_correspondences.diff(t.ancestors).isEmpty &&
              t.ancestors.diff(anc_correspondences).isEmpty
          }

          val rsmap = find_matching(clause.negative.toList, inference.root.negative.toList, matcher) ++
            find_matching(clause.positive.toList, inference.root.positive.toList, matcher)

          extendw_pmap(p, rpmap, rsmap, inference)


        case Resolution(clause, parent1, parent2, lit1, lit2, sub) =>
          val (rpmap1, rmap1, rparent1) = if (pmap contains parent1) add_pmap(pmap, parent1) else rename_resproof(parent1, irules, smap, pmap)
          val (rpmap2, rmap2, rparent2) = if (pmap contains parent2) add_pmap(pmap, parent2) else rename_resproof(parent2, irules, smap, rpmap1)
          val nsub = Substitution(sub.map map ((x:(Var, FOLExpression)) => (x._1, apply(x._2, smap)) ))
          val inference = Resolution(rparent1, rparent2, rmap1(lit1), rmap2(lit2), nsub)
          val rmap = rmap1 ++ rmap2

          def matcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = {
            //println("anc matcher")
            //println(o); println(o.ancestors)
            //println(t); println(t.ancestors)
            val anc_correspondences : immutable.Seq[FormulaOccurrence] = o.ancestors.map(rmap)
            //println(anc_correspondences)
            t.formula == apply(o.formula, smap) &&
              anc_correspondences.diff(t.ancestors).isEmpty &&
              t.ancestors.diff(anc_correspondences).isEmpty
          }

          val rsmap = find_matching(clause.negative.toList, inference.root.negative.toList, matcher) ++
            find_matching(clause.positive.toList, inference.root.positive.toList, matcher)

          extendw_pmap(p, rpmap2, rsmap, inference)



        case Paramodulation(clause, parent1, parent2, lit1, lit2, sub) =>
          val (rpmap1, rmap1, rparent1) = if (pmap contains parent1) add_pmap(pmap, parent1) else rename_resproof(parent1, irules, smap, pmap)
          val (rpmap2, rmap2, rparent2) = if (pmap contains parent2) add_pmap(pmap, parent2) else rename_resproof(parent2, irules, smap, rpmap1)

          val nsub = Substitution(sub.map map ((x:(Var, FOLExpression)) => (x._1, apply(x._2, smap)) ))

          val Some(prim) = clause.literals.map(_._1).find( occ => occ.ancestors == List(lit1,lit2) || occ.ancestors == List(lit2,lit1) )
          val nformula = apply(prim.formula, smap).asInstanceOf[FOLFormula]

          val inference = Paramodulation(rparent1, rparent2, rmap1(lit1), rmap2(lit2), nformula, nsub)
          val rmap = rmap1 ++ rmap2

          def matcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = {
            //println("anc matcher")
            //println(o); println(o.ancestors)
            //println(t); println(t.ancestors)
            val anc_correspondences : immutable.Seq[FormulaOccurrence] = o.ancestors.map(rmap)
            //println(anc_correspondences)
            t.formula == apply(o.formula, smap) &&
              anc_correspondences.diff(t.ancestors).isEmpty &&
              t.ancestors.diff(anc_correspondences).isEmpty
          }

          val rsmap = find_matching(clause.negative.toList, inference.root.negative.toList, matcher) ++
            find_matching(clause.positive.toList, inference.root.positive.toList, matcher)

          extendw_pmap(p, rpmap2, rsmap, inference)

*/
      }
  }

}
