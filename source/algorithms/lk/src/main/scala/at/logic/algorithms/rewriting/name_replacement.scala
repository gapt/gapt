package at.logic.algorithms.rewriting

import at.logic.language.lambda.typedLambdaCalculus.{Abs, App, Var, LambdaExpression}
import at.logic.language.hol.logicSymbols.{ConstantSymbolA, ConstantStringSymbol}
import at.logic.language.lambda.types._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.resolution.robinson._
import at.logic.calculi.resolution.base.Clause
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.hol.HOLFormula
import at.logic.language.fol.{FOLExpression, FOLTerm, FOLFormula}
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import scala.Some
import at.logic.language.lambda.types.->
import at.logic.calculi.resolution.instance.Instance

/**
 * performs renaming of constants, functions and predicate symbols
 */
object NameReplacement {

  def apply[T <: LambdaExpression](exp : T, map : SymbolMap) : T = rename_symbols(exp, map)
  def apply(fs: FSequent, map : SymbolMap) = rename_fsequent(fs,map)
  def apply(p : RobinsonResolutionProof, map : SymbolMap) : RobinsonResolutionProof = {
    //don't process the proof if there is nothing to do
    if (map.isEmpty) p else rename_resproof(p, map)._2
  }

  // map from sumbol name to pair of Arity and replacement symbol name
  type SymbolMap = Map[String, (Int,String)]
  val emptySymbolMap = Map[String, (Int,String)]()

  //gives the airty of a function - simple types have arity 0, complex types have 1 + arity of return value (because
  // of currying)
  def arity(t:TA) : Int = t match {
    case t1 -> t2 => 1 + arity(t2)
    case _ => 0
  }

  def rename_symbols[T <: LambdaExpression](exp : T, map : SymbolMap) : T = exp match {
    case Var(symbol, exptype) =>
      symbol match {
        case ConstantStringSymbol(name) => map.get(name) match {
          case Some((rarity,rname)) =>

            if (arity(exptype) == rarity) {
              //println("replacing "+name+" by "+map(name))
              exp.factory.createVar(new ConstantStringSymbol(rname), exptype).asInstanceOf[T]
            }
            else {
              exp
            }
          case None => exp
        }
        case _ => exp
      }

    case App(exp1,exp2) =>
      exp.factory.createApp(rename_symbols(exp1, map), rename_symbols(exp2,map)).asInstanceOf[T]
    case Abs(v, exp1) =>
      // abstractions are always over variables
      exp.factory.createAbs(v, rename_symbols(exp1, map)).asInstanceOf[T]
  }
  def rename_fsequent(fs: FSequent, map : SymbolMap) = FSequent(fs.antecedent map (rename_symbols(_,map)), fs.succedent map (rename_symbols(_,map)))
  def rename_substitution[T <: LambdaExpression](sub : Substitution[T], map : SymbolMap) : Substitution[T] = {
    Substitution[T](for ( (key,value) <- sub.map) yield { (key, apply(value, map)) } )
  }

  type OccMap = Map[FormulaOccurrence, FormulaOccurrence]
  type ProofMap = Map[RobinsonResolutionProof, (OccMap, RobinsonResolutionProof)]
  val emptyProofMap = Map[RobinsonResolutionProof, (OccMap, RobinsonResolutionProof)]()

  def extendw_pmap(index: RobinsonResolutionProof, p:ProofMap, o : OccMap, i : RobinsonResolutionProof) = (p + ((index,(o,i))), o, i)
  def add_pmap(pmap : ProofMap, parent: RobinsonResolutionProof) : (ProofMap, OccMap, RobinsonResolutionProof) = { val x=pmap(parent); (pmap, x._1, x._2) }

  def rename_resproof(p : RobinsonResolutionProof, smap : SymbolMap) : (OccMap, RobinsonResolutionProof) = rename_resproof(p, smap, emptyProofMap)._1(p)

  def rename_resproof(p : RobinsonResolutionProof, smap : SymbolMap, pmap : ProofMap)  : (ProofMap, OccMap, RobinsonResolutionProof) = {
    if (pmap contains p) add_pmap(pmap,p) else
    p match {
    case InitialClause(clause) =>
      //rename literals
      val negp : List[FOLFormula] = clause.negative.toList map ((fo : FormulaOccurrence) =>apply(fo.formula.asInstanceOf[FOLFormula], smap))
      val posp : List[FOLFormula] = clause.positive.toList map ((fo : FormulaOccurrence) =>apply(fo.formula.asInstanceOf[FOLFormula], smap))
      val inference = InitialClause(negp, posp)
      //create map form original iteral occs to renamed literal occs
      val negm : Map[FormulaOccurrence, FOLFormula] = Map[FormulaOccurrence, FOLFormula]() ++ (clause.negative zip negp)
      val posm : Map[FormulaOccurrence, FOLFormula] = Map[FormulaOccurrence, FOLFormula]() ++ (clause.positive zip posp)
      def nmatcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = negm(o) == t.formula
      def pmatcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = posm(o) == t.formula

      //println(negm ++ posm)
      //println(clause)
      //println(inference.root)
      val rsmap = find_matching(clause.negative.toList, inference.root.negative.toList, nmatcher) ++
                  find_matching(clause.positive.toList, inference.root.positive.toList, pmatcher)

      extendw_pmap(p, pmap, rsmap, inference)



    case Variant(clause, parent1, sub) =>
      val (rpmap, rmap, rparent1) = if (pmap contains parent1) add_pmap(pmap, parent1) else rename_resproof(parent1, smap, pmap)
      val nsub = Substitution(sub.map map ((x:(Var, FOLExpression)) => (x._1, apply(x._2, smap)) ))
      var inference :RobinsonResolutionProof = Variant(rparent1, nsub)

      def matcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = {
        val anc_correspondences : Seq[FormulaOccurrence] = o.ancestors.map(rmap)
        t.formula == apply(o.formula, smap) &&
          anc_correspondences.diff(t.ancestors).isEmpty &&
          t.ancestors.diff(anc_correspondences).isEmpty
      }

      val rsmap = find_matching(clause.negative.toList, inference.root.negative.toList, matcher) ++
        find_matching(clause.positive.toList, inference.root.positive.toList, matcher)

      extendw_pmap(p, rpmap, rsmap, inference)


    case Factor(clause, parent1, aux, sub) =>
      val (rpmap, rmap, rparent1) = if (pmap contains parent1) add_pmap(pmap, parent1) else rename_resproof(parent1, smap, pmap)
      val nsub = Substitution(sub.map map ((x:(Var, FOLExpression)) => (x._1, apply(x._2, smap)) ))
      var inference :RobinsonResolutionProof = aux match {
        case lit1 :: Nil =>
          Factor(rparent1, rmap(lit1.head), lit1.tail map rmap, nsub)
        case lit1::lit2::Nil =>
          Factor(rparent1, rmap(lit1.head), lit1.tail map rmap, rmap(lit2.head), lit2.tail map rmap, nsub)
        case _ => throw new Exception("Factor rule for "+p.root+" does not have one or two primary formulas! aux="+aux)
      }

      def matcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = {
        val anc_correspondences : Seq[FormulaOccurrence] = o.ancestors.map(rmap)
        t.formula == apply(o.formula, smap) &&
          anc_correspondences.diff(t.ancestors).isEmpty &&
          t.ancestors.diff(anc_correspondences).isEmpty
      }

      val rsmap = find_matching(clause.negative.toList, inference.root.negative.toList, matcher) ++
        find_matching(clause.positive.toList, inference.root.positive.toList, matcher)

      extendw_pmap(p, rpmap, rsmap, inference)

    case Instance(clause, parent1, sub) =>
      val (rpmap, rmap, rparent1) = if (pmap contains parent1) add_pmap(pmap, parent1) else rename_resproof(parent1, smap, pmap)
      val nsub = Substitution(sub.map map ((x:(Var, FOLExpression)) => (x._1, apply(x._2, smap)) ))
      var inference :RobinsonResolutionProof =  Instance(rparent1, nsub)

      def matcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = {
        val anc_correspondences : Seq[FormulaOccurrence] = o.ancestors.map(rmap)
        t.formula == apply(o.formula, smap) &&
          anc_correspondences.diff(t.ancestors).isEmpty &&
          t.ancestors.diff(anc_correspondences).isEmpty
      }

      val rsmap = find_matching(clause.negative.toList, inference.root.negative.toList, matcher) ++
        find_matching(clause.positive.toList, inference.root.positive.toList, matcher)

      extendw_pmap(p, rpmap, rsmap, inference)


    case Resolution(clause, parent1, parent2, lit1, lit2, sub) =>
      val (rpmap1, rmap1, rparent1) = if (pmap contains parent1) add_pmap(pmap, parent1) else rename_resproof(parent1, smap, pmap)
      val (rpmap2, rmap2, rparent2) = if (pmap contains parent2) add_pmap(pmap, parent2) else rename_resproof(parent2, smap, rpmap1)
      val nsub = Substitution(sub.map map ((x:(Var, FOLExpression)) => (x._1, apply(x._2, smap)) ))
      val inference = Resolution(rparent1, rparent2, rmap1(lit1), rmap2(lit2), nsub)
      val rmap = rmap1 ++ rmap2

      def matcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = {
        //println("anc matcher")
        //println(o); println(o.ancestors)
        //println(t); println(t.ancestors)
        val anc_correspondences : Seq[FormulaOccurrence] = o.ancestors.map(rmap)
        //println(anc_correspondences)
        t.formula == apply(o.formula, smap) &&
        anc_correspondences.diff(t.ancestors).isEmpty &&
        t.ancestors.diff(anc_correspondences).isEmpty
      }

      val rsmap = find_matching(clause.negative.toList, inference.root.negative.toList, matcher) ++
                  find_matching(clause.positive.toList, inference.root.positive.toList, matcher)

      extendw_pmap(p, rpmap2, rsmap, inference)



    case Paramodulation(clause, parent1, parent2, lit1, lit2, _, sub) =>
      val (rpmap1, rmap1, rparent1) = if (pmap contains parent1) add_pmap(pmap, parent1) else rename_resproof(parent1, smap, pmap)
      val (rpmap2, rmap2, rparent2) = if (pmap contains parent2) add_pmap(pmap, parent2) else rename_resproof(parent2, smap, rpmap1)

      val nsub = Substitution(sub.map map ((x:(Var, FOLExpression)) => (x._1, apply(x._2, smap)) ))

      val Some(prim) = clause.literals.map(_._1).find( occ => occ.ancestors == List(lit1,lit2) || occ.ancestors == List(lit2,lit1) )
      val nformula = apply(prim.formula, smap).asInstanceOf[FOLFormula]

      val inference = Paramodulation(rparent1, rparent2, rmap1(lit1), rmap2(lit2), nformula, nsub)
      val rmap = rmap1 ++ rmap2

      def matcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = {
        //println("anc matcher")
        //println(o); println(o.ancestors)
        //println(t); println(t.ancestors)
        val anc_correspondences : Seq[FormulaOccurrence] = o.ancestors.map(rmap)
        //println(anc_correspondences)
        t.formula == apply(o.formula, smap) &&
          anc_correspondences.diff(t.ancestors).isEmpty &&
          t.ancestors.diff(anc_correspondences).isEmpty
      }

      val rsmap = find_matching(clause.negative.toList, inference.root.negative.toList, matcher) ++
        find_matching(clause.positive.toList, inference.root.positive.toList, matcher)

      extendw_pmap(p, rpmap2, rsmap, inference)

  }
  }



  /* creates a mapping from elements in objects to targets. the predicate matches indicates when two elements should
     be considered to match each */
  def find_matching[A,B](objects : List[A], targets : List[B], matches : (A,B) => Boolean  ) : Map[A,B] = {
    objects match {
      case x::xs =>
        val (prefix, suffix) = targets.span(!matches(x,_))
        suffix match {
          case el::rest => find_matching(xs, prefix ++ rest, matches) + ((x,el))
          case Nil =>  throw new Exception("Can not find a match for element "+x+" in "+targets)
        }

      case Nil =>
        if (targets.isEmpty)
          Map[A,B]()
        else
          throw new Exception("Want to create a matching of sets of different size! remaining elements: "+targets)
    }
  }

}
