package at.logic.algorithms.rewriting

import at.logic.language.lambda.types._
import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.resolution.robinson._
import at.logic.calculi.resolution.Clause
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.language.hol.{HOLVar, HOLConst, Atom, Function, And, Equation, Or, Imp, Neg, ExVar, AllVar, HOLExpression, HOLFormula}
import at.logic.language.fol.{FOLVar, FOLConst, Atom=>FOLAtom, Function=>FOLFunction, And=>FOLAnd, Equation=>FOLEquation, Or=>FOLOr, Imp=>FOLImp, Neg=>FOLNeg, ExVar=>FOLExVar, AllVar=>FOLAllVar, FOLExpression, FOLTerm, FOLFormula, Substitution}
import at.logic.language.lambda.symbols.StringSymbol

/**
 * performs renaming of constants, functions and predicate symbols
 */
object NameReplacement {

  def apply(exp : HOLExpression, map : SymbolMap) : HOLExpression = rename_symbols(exp, map)
  def apply(exp : FOLExpression, map : SymbolMap) : FOLExpression = rename_symbols(exp, map)
  def apply(exp : HOLFormula, map : SymbolMap) : HOLFormula = rename_symbols(exp, map)
  def apply(exp : FOLFormula, map : SymbolMap) : FOLFormula = rename_symbols(exp, map)

  def apply(fs: FSequent, map : SymbolMap) = rename_fsequent(fs,map)
  def apply(p : RobinsonResolutionProof, map : SymbolMap) : RobinsonResolutionProof = {
    //don't process the proof if there is nothing to do
    if (map.isEmpty) p else rename_resproof(p, map)._2
  }

  // map from symbol name to pair of Arity and replacement symbol name
  type SymbolMap = Map[String, (Int,String)]
  val emptySymbolMap = Map[String, (Int,String)]()

  // The following code is duplicated because there is a class cast exception
  // in one of the tests if I have only the one for HOL. The problem is the 
  // reconstruction of constants. Create a method that changes only the names
  // in the objects without re-instantiating it??
  // It seems this is used only for FOL though...
  // TODO: think of a way to implement this and remove the duplication.

  def rename_symbols(exp: HOLExpression, map: SymbolMap) : HOLExpression = exp match {
    
    case HOLVar(_, _) => exp
    
    case HOLConst(name, exptype) => map.get(name) match {
      case Some((rarity, rname)) =>
        if (Arity(exptype) == rarity) {
          HOLConst(StringSymbol(rname), exptype)
        }
        else {
          exp
        }
      case None => exp
    }

    case Atom(x: HOLVar, args) => Atom(x, args.map(a => rename_symbols(a, map)))
    case Atom(x: HOLConst, args) => Atom(rename_symbols(x, map).asInstanceOf[HOLConst], args.map(a => rename_symbols(a, map)))
    case Function(x: HOLVar, args, _) => Function(x, args.map(a => rename_symbols(a, map)))
    case Function(x: HOLConst, args, _) => Function(rename_symbols(x, map).asInstanceOf[HOLConst], args.map(a => rename_symbols(a, map)))
    case And(x,y) => And(rename_symbols(x, map), rename_symbols(y, map))
    case Equation(x,y) => Equation(rename_symbols(x, map), rename_symbols(y, map))
    case Or(x,y) => Or(rename_symbols(x, map), rename_symbols(y, map))
    case Imp(x,y) => Imp(rename_symbols(x, map), rename_symbols(y, map))
    case Neg(x) => Neg(rename_symbols(x, map))
    // Variables are not renamed
    case ExVar(x,f) => ExVar(x, rename_symbols(f, map))
    case AllVar(x,f) => AllVar(x, rename_symbols(f, map))
  }

  def rename_symbols(exp: FOLExpression, map: SymbolMap) : FOLExpression = exp match {
    
    case FOLVar(_) => exp
    
    case FOLConst(name) => map.get(name) match {
      case Some((rarity, rname)) =>
        if (Arity(exp.exptype) == rarity) {
          FOLConst(StringSymbol(rname))
        }
        else {
          exp
        }
      case None => exp
    }

    case FOLAtom(x, args) => map.get(x.toString) match {
      case Some((rarity, rname)) =>
        if (args.length == rarity) {
          FOLAtom(StringSymbol(rname), args.map(a => rename_symbols(a, map).asInstanceOf[FOLTerm]))
        }
        else {
          FOLAtom(x, args.map(a => rename_symbols(a, map).asInstanceOf[FOLTerm]))
        }
      case None => FOLAtom(x, args.map(a => rename_symbols(a, map).asInstanceOf[FOLTerm]))
    }

    case FOLFunction(x, args) => map.get(x.toString) match {
      case Some((rarity, rname)) =>
        if (args.length == rarity) {
          FOLFunction(StringSymbol(rname), args.map(a => rename_symbols(a, map).asInstanceOf[FOLTerm]))
        }
        else {
          FOLFunction(x, args.map(a => rename_symbols(a, map).asInstanceOf[FOLTerm]))
        }
      case None => FOLFunction(x, args.map(a => rename_symbols(a, map).asInstanceOf[FOLTerm]))
    }
    case FOLAnd(x,y) => FOLAnd(rename_symbols(x, map), rename_symbols(y, map))
    case FOLEquation(x,y) => FOLEquation(rename_symbols(x, map).asInstanceOf[FOLTerm], rename_symbols(y, map).asInstanceOf[FOLTerm])
    case FOLOr(x,y) => FOLOr(rename_symbols(x, map), rename_symbols(y, map))
    case FOLImp(x,y) => FOLImp(rename_symbols(x, map), rename_symbols(y, map))
    case FOLNeg(x) => FOLNeg(rename_symbols(x, map))
    // Variables are not renamed
    case FOLExVar(x,f) => FOLExVar(x, rename_symbols(f, map))
    case FOLAllVar(x,f) => FOLAllVar(x, rename_symbols(f, map))
  }

  def rename_symbols(exp : HOLFormula, map : SymbolMap) : HOLFormula =
    rename_symbols(exp.asInstanceOf[HOLExpression],map).asInstanceOf[HOLFormula]

  def rename_symbols(exp : FOLFormula, map : SymbolMap) : FOLFormula =
    rename_symbols(exp.asInstanceOf[FOLExpression],map).asInstanceOf[FOLFormula]

  // Yes, this sucks. But it was the easiest and fastest way to deal with 
  // FSequents which are supposed to have FOLFormulas instead of HOLFormulas.
  def rename_symbols_bla(f: HOLFormula, map: SymbolMap) = f.isInstanceOf[FOLFormula] match {
    case true => rename_symbols(f.asInstanceOf[FOLFormula], map)
    case false => rename_symbols(f, map)
  }

  def rename_fsequent(fs: FSequent, map : SymbolMap) =
    FSequent(fs.antecedent map (rename_symbols_bla(_,map)), fs.succedent map (rename_symbols_bla(_,map)))

  //def rename_substitution(sub : Substitution, map : SymbolMap) : Substitution = {
  //  Substitution(for ( (key,value) <- sub.map) yield { (key, apply(value, map)) } )
  //}

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
      val nsub = Substitution(sub.folmap map (x => (x._1, apply(x._2, smap)) ))
      var inference :RobinsonResolutionProof = Variant(rparent1, nsub)

      def matcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = {
        val anc_correspondences : Seq[FormulaOccurrence] = o.parents.map(rmap)
        t.formula == apply(o.formula.asInstanceOf[FOLFormula], smap) &&
          anc_correspondences.diff(t.parents).isEmpty &&
          t.parents.diff(anc_correspondences).isEmpty
      }

      val rsmap = find_matching(clause.negative.toList, inference.root.negative.toList, matcher) ++
        find_matching(clause.positive.toList, inference.root.positive.toList, matcher)

      extendw_pmap(p, rpmap, rsmap, inference)


    case Factor(clause, parent1, aux, sub) =>
      val (rpmap, rmap, rparent1) = if (pmap contains parent1) add_pmap(pmap, parent1) else rename_resproof(parent1, smap, pmap)
      val nsub = Substitution(sub.folmap map (x => (x._1, apply(x._2, smap)) ))
      var inference :RobinsonResolutionProof = aux match {
        case lit1 :: Nil =>
          Factor(rparent1, rmap(lit1.head), lit1.tail map rmap, nsub)
        case lit1::lit2::Nil =>
          Factor(rparent1, rmap(lit1.head), lit1.tail map rmap, rmap(lit2.head), lit2.tail map rmap, nsub)
        case _ => throw new Exception("Factor rule for "+p.root+" does not have one or two primary formulas! aux="+aux)
      }

      def matcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = {
        val anc_correspondences : Seq[FormulaOccurrence] = o.parents.map(rmap)
        t.formula == apply(o.formula.asInstanceOf[FOLFormula], smap) &&
          anc_correspondences.diff(t.parents).isEmpty &&
          t.parents.diff(anc_correspondences).isEmpty
      }

      val rsmap = find_matching(clause.negative.toList, inference.root.negative.toList, matcher) ++
        find_matching(clause.positive.toList, inference.root.positive.toList, matcher)

      extendw_pmap(p, rpmap, rsmap, inference)

    case Instance(clause, parent1, sub) =>
      val (rpmap, rmap, rparent1) = if (pmap contains parent1) add_pmap(pmap, parent1) else rename_resproof(parent1, smap, pmap)
      val nsub = Substitution(sub.folmap map (x => (x._1, apply(x._2, smap)) ))
      var inference :RobinsonResolutionProof =  Instance(rparent1, nsub)

      def matcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = {
        val anc_correspondences : Seq[FormulaOccurrence] = o.parents.map(rmap)
        t.formula == apply(o.formula.asInstanceOf[FOLFormula], smap) &&
          anc_correspondences.diff(t.parents).isEmpty &&
          t.parents.diff(anc_correspondences).isEmpty
      }

      val rsmap = find_matching(clause.negative.toList, inference.root.negative.toList, matcher) ++
        find_matching(clause.positive.toList, inference.root.positive.toList, matcher)

      extendw_pmap(p, rpmap, rsmap, inference)


    case Resolution(clause, parent1, parent2, lit1, lit2, sub) =>
      val (rpmap1, rmap1, rparent1) = if (pmap contains parent1) add_pmap(pmap, parent1) else rename_resproof(parent1, smap, pmap)
      val (rpmap2, rmap2, rparent2) = if (pmap contains parent2) add_pmap(pmap, parent2) else rename_resproof(parent2, smap, rpmap1)
      val nsub = Substitution(sub.folmap map (x => (x._1, apply(x._2, smap)) ))
      val inference = Resolution(rparent1, rparent2, rmap1(lit1), rmap2(lit2), nsub)
      val rmap = rmap1 ++ rmap2

      def matcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = {
        //println("anc matcher")
        //println(o); println(o.ancestors)
        //println(t); println(t.ancestors)
        val anc_correspondences : Seq[FormulaOccurrence] = o.parents.map(rmap)
        //println(anc_correspondences)
        t.formula == apply(o.formula.asInstanceOf[FOLFormula], smap) &&
        anc_correspondences.diff(t.parents).isEmpty &&
        t.parents.diff(anc_correspondences).isEmpty
      }

      val rsmap = find_matching(clause.negative.toList, inference.root.negative.toList, matcher) ++
                  find_matching(clause.positive.toList, inference.root.positive.toList, matcher)

      extendw_pmap(p, rpmap2, rsmap, inference)



    case Paramodulation(clause, parent1, parent2, lit1, lit2, _, sub) =>
      val (rpmap1, rmap1, rparent1) = if (pmap contains parent1) add_pmap(pmap, parent1) else rename_resproof(parent1, smap, pmap)
      val (rpmap2, rmap2, rparent2) = if (pmap contains parent2) add_pmap(pmap, parent2) else rename_resproof(parent2, smap, rpmap1)

      val nsub = Substitution(sub.folmap map (x => (x._1, apply(x._2, smap)) ))

      val Some(prim) = clause.literals.map(_._1).find( occ => occ.parents == List(lit1,lit2) || occ.parents == List(lit2,lit1) )
      val nformula = apply(prim.formula.asInstanceOf[FOLFormula], smap)

      val inference = Paramodulation(rparent1, rparent2, rmap1(lit1), rmap2(lit2), nformula, nsub)
      val rmap = rmap1 ++ rmap2

      def matcher(o : FormulaOccurrence, t : FormulaOccurrence) : Boolean = {
        //println("anc matcher")
        //println(o); println(o.ancestors)
        //println(t); println(t.ancestors)
        val anc_correspondences : Seq[FormulaOccurrence] = o.parents.map(rmap)
        //println(anc_correspondences)
        t.formula == apply(o.formula.asInstanceOf[FOLFormula], smap) &&
          anc_correspondences.diff(t.parents).isEmpty &&
          t.parents.diff(anc_correspondences).isEmpty
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
