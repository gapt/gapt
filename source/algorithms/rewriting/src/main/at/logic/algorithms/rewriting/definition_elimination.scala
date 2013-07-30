package at.logic.algorithms.rewriting

import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.language.hol._
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.symbols.SymbolA

object defintion_elimination {
  type DefinitionsMap = Map[HOLFormula, HOLFormula]
  type ProcessedDefinitionsMap = Map[SymbolA, (List[HOLVar], HOLFormula)]

  def fixedpoint_val[A](f : (A=>A), l : A) : A = {
    val r = f(l)
    if (r==l) r  else fixedpoint_val(f,r)
  }

  def fixedpoint_seq[A](f : (A=>A), l : Seq[A] ) : Seq[A] = {
    val r = l map f
    if (r==l) r  else fixedpoint_seq(f,r)
  }

  def recursive_elimination_from(defs: DefinitionsMap, l : FSequent) : FSequent =
    FSequent(recursive_elimination_from(defs,l._1), recursive_elimination_from(defs,l._2))

  def recursive_elimination_from(defs: DefinitionsMap, l : Seq[HOLFormula]) : Seq[HOLFormula] =
    fixedpoint_seq(((x:HOLFormula) => eliminate_from(defs,x)), l )

  def recursive_elimination_from(defs: DefinitionsMap, l : HOLFormula) : HOLFormula =
    fixedpoint_val(((x:HOLFormula) => eliminate_from(defs,x)), l )


  def eliminate_from(defs : DefinitionsMap, f : HOLFormula) : HOLFormula = {
    //preprocess definitions
    var map : ProcessedDefinitionsMap = Map[SymbolA, (List[HOLVar], HOLFormula)]()
    //TODO: expand definitions in map
    for (k <- defs.keys) k match {
      case Atom(sym, args) =>
        if (args forall (_.isInstanceOf[HOLVar]))
          map = map + Tuple2(sym, (args.asInstanceOf[List[HOLVar]], defs(k)))
        else
          println("Warning: arguments of definition are not variables!")
        args.filterNot(_.isInstanceOf[HOLVar]) map println
      case _ => println("Warning: ignoring non-atomic definition during definition elimination!")
    }
    eliminate_from_(map, f)
  }

  private def eliminate_from_(defs : ProcessedDefinitionsMap, f : HOLFormula) : HOLFormula = {
    f match {
      case Atom(sym, args) =>
        defs.get(sym) match {
          case Some((definition_args, defined_formula)) =>
            if (args.length != definition_args.length) {
              println("Warning: ignoring definition replacement because argument numbers dont match!")
              f
            } else {
              //we need to insert the correct values for the free variables in the definition
              //the casting is needed since we cannot make a map covariant
              //val pairs = (definition_args zip args)  filter ((x:(HOLExpression, HOLExpression) ) => x._1.isInstanceOf[HOLVar])
              val pairs = definition_args zip  args
              val sub = Substitution(pairs)
              println("Substitution:")
              println(sub)
              sub.apply(defined_formula).asInstanceOf[HOLFormula]
            }
          case _ => f
        }
      case Neg(f1) => Neg(eliminate_from_(defs, f1))
      case AllVar(q,f1) => AllVar(q, eliminate_from_(defs, f1))
      case ExVar(q,f1) => ExVar(q, eliminate_from_(defs, f1))
      case And(f1,f2) => And(eliminate_from_(defs, f1), eliminate_from_(defs, f2))
      case Imp(f1,f2) => Imp(eliminate_from_(defs, f1), eliminate_from_(defs, f2))
      case Or(f1,f2)  => Or(eliminate_from_(defs, f1), eliminate_from_(defs, f2))
      case _ => println("Warning: unhandled case in definition elimination!"); f
    }
  }


  private def append_ancestors(endsequent : FSequent, ancestors : Sequent) =
    Sequent(append_ancestors_(endsequent._1, ancestors.antecedent),
      append_ancestors_(endsequent._2, ancestors.succedent))
  private def append_ancestors_(endsequent : Seq[HOLFormula], ancestors : Seq[FormulaOccurrence]) :
  Seq[FormulaOccurrence] = {
    endsequent.zip(ancestors).map(
      (x:(HOLFormula, FormulaOccurrence)) =>
        x._2.factory.createFormulaOccurrence(x._1, Seq(x._2)  )  )
  }

  //needs a different name because type erasure removes HOLFormula/FormulaOccurrence from append_ancestors(2)_
  private def append_ancestors2(endsequent : Sequent, ancestors : Sequent) =
    Sequent(append_ancestors2_(endsequent.antecedent, ancestors.antecedent),
      append_ancestors2_(endsequent.succedent, ancestors.succedent))
  private def append_ancestors2_(endsequent : Seq[FormulaOccurrence], ancestors : Seq[FormulaOccurrence]) :
  Seq[FormulaOccurrence] = {
    endsequent.zip(ancestors).map(
      (x:(FormulaOccurrence, FormulaOccurrence)) =>
        x._2.factory.createFormulaOccurrence(x._1.formula, x._1.ancestors ++ x._2.ancestors  )  )
  }



  /* calculates the correspondences between occurences of the formulas in the original end-sequent and those in the
 *  definition free one. in binary rules, ancestors may occur in both branches, so we also pass a map with previously
 *  calculated correspondences and add the new ones
 private def calculateCorrespondences2(rewrite : (HOLFormula => HOLFormula),
                                      existing_correspondences : Map[FormulaOccurrence, FormulaOccurrence],
                                      root: Sequent, duproof: LKProof)
   : Map[FormulaOccurrence, FormulaOccurrence] = {
   val fsroot = root.toFSequent()
   val eroot_fs = FSequent(fsroot.antecedent map rewrite, fsroot.succedent map rewrite)
   val eroot_f = append_ancestors(eroot_fs, duproof.root)
   val additional = (root.antecedent ++ root.succedent) zip (eroot_f.antecedent ++ eroot_f.succedent)
   var correspondences = existing_correspondences
   for ( el@(key,value) <- additional ) {
     //if there are ancestors in both subproofs, the entry needs to be merged
     if (correspondences.contains(key)) {
       val entry = correspondences(key)
       correspondences = correspondences + ((key,(new FormulaOccurrence(entry.formula, entry.ancestors ++ value.ancestors, entry.factory))))

     } else {
       correspondences = correspondences + el
     }

   }

   correspondences
 } */



}
