package at.logic.algorithms.rewriting

import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.language.fol
import at.logic.language.hol._
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.symbols.SymbolA
import at.logic.language.lambda.typedLambdaCalculus.{Abs, App, Var, LambdaExpression}
import at.logic.algorithms.matching.hol.NaiveIncompleteMatchingAlgorithm
import at.logic.language.fol.FOLFormula

object definition_elimination {
  type DefinitionsMap = Map[HOLExpression, HOLExpression]
  type ProcessedDefinitionsMap = Map[SymbolA, (List[HOLVar], HOLFormula)]

  def fixedpoint_val[A](f : (A=>A), l : A) : A = {
    val r = f(l)
    if (r==l) r  else fixedpoint_val(f,r)
  }

  def fixedpoint_seq[A](f : (A=>A), l : Seq[A] ) : Seq[A] = {
    val r = l map f
    if (r==l) r  else fixedpoint_seq(f,r)
  }

  /*
  def recursive_elimination_from(defs: DefinitionsMap, l : FSequent) : FSequent =
    FSequent(recursive_elimination_from(defs,l._1), recursive_elimination_from(defs,l._2))

  def recursive_elimination_from(defs: DefinitionsMap, l : Seq[HOLFormula]) : Seq[HOLFormula] =
    fixedpoint_seq(((x:HOLFormula) => eliminate_from(defs,x)), l )

  def recursive_elimination_from(defs: DefinitionsMap, l : HOLFormula) : HOLFormula =
    fixedpoint_val(((x:HOLFormula) => eliminate_from(defs,x)), l )
    */

  private def c(e:HOLExpression) = {
    if (e.isInstanceOf[HOLFormula]) e.asInstanceOf[HOLFormula] else
      throw new Exception("Could not convert "+e+" to a HOL Formula!")
  }

  def replaceAll_informula(dmap: DefinitionsMap, e:HOLFormula) : HOLFormula = c(replaceAll_in(dmap,e))
  def replaceAll_in(dmap : DefinitionsMap, e : HOLExpression) : HOLExpression = {
    e match {
      case HOLConst(_,_) => try_to_match(dmap, e)
      case HOLVar(_,_) => try_to_match(dmap, e)
      case Neg(s) => Neg(replaceAll_informula(dmap,s))
      case And(s,t) => And(replaceAll_informula(dmap,s), replaceAll_informula(dmap,t))
      case Or(s,t) => Or(replaceAll_informula(dmap,s), replaceAll_informula(dmap,t))
      case Imp(s,t) => Imp(replaceAll_informula(dmap,s), replaceAll_informula(dmap,t))
      //TODO: fix issue 224 and remove the fol specific matches
      case fol.AllVar(x,t) => fol.AllVar(x, replaceAll_informula(dmap, t).asInstanceOf[FOLFormula])
      case fol.ExVar(x,t) => fol.ExVar(x, replaceAll_informula(dmap, t).asInstanceOf[FOLFormula])
      case AllVar(x,t) => AllVar(x, replaceAll_informula(dmap, t))
      case ExVar(x,t) => ExVar(x, replaceAll_informula(dmap, t))
      case HOLApp(s,t) =>
        val fullmatch = try_to_match(dmap,e)
        if (fullmatch == e)
          try_to_match(dmap,e.factory.createApp(replaceAll_in(dmap, s), replaceAll_in(dmap,t)).asInstanceOf[HOLExpression])
        else
          replaceAll_in(dmap,fullmatch)
      case HOLAbs(x,t) => e.factory.createAbs(x, replaceAll_in(dmap, t)).asInstanceOf[HOLExpression]
    }
  }


  def try_to_matchformula(dmap:DefinitionsMap,e:HOLExpression) = c(try_to_match(dmap,e))
  def try_to_match(dmap: DefinitionsMap, e: HOLExpression): HOLExpression = {
    dmap.keys.foldLeft(e)((v, elem) => {
      //println("matching "+elem+" against "+v)
      NaiveIncompleteMatchingAlgorithm.holMatch(elem,v)(Nil) match {
        case None => v
        case Some(sub) =>
          val r = sub(dmap(elem))
          //println("YES! "+sub)
          r
      }
    }
    )
  }

  def expand_dmap(dmap: DefinitionsMap) : DefinitionsMap = {
    val ndmap = dmap map ( x => {
      (x._1, replaceAll_in(dmap, x._2))
    })

    if (ndmap == dmap)
      dmap
    else expand_dmap(ndmap)
  }

  /*
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
  } */

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



}
