package at.logic.algorithms.unification

import _root_.at.logic.calculi.lk.base.FSequent
import _root_.at.logic.calculi.lk.base.types.FSequent
import _root_.at.logic.calculi.lkmodulo.types.Equation
import _root_.at.logic.calculi.lkmodulo.{EequalityA, Equation}
import _root_.at.logic.language.hol.{HOLFormula}
import _root_.at.logic.language.lambda.symbols.{VariableStringSymbol, VariableSymbolA}
import _root_.at.logic.parsing.language.simple.SimpleFOLParser
import _root_.at.logic.parsing.readers.StringReader
import at.logic.algorithms.diophantine.{LankfordSolver, Vector}
import at.logic.language.hol.logicSymbols.{ConstantStringSymbol, ConstantSymbolA}
import at.logic.language.fol._
import at.logic.language.fol.{Equation => FOLEquation}
import at.logic.language.lambda.substitutions.Substitution
import scala.collection.immutable.Seq

import collection.mutable.HashMap
import collection.immutable.Stream.Cons

object ACUnification {
  val algorithms  = new HashMap[ConstantSymbolA, FinitaryUnification[FOLTerm]]
  def unify(f:ConstantSymbolA, term1:FOLTerm, term2:FOLTerm) : Seq[Substitution[FOLTerm]] = {
    if (! (algorithms contains f)) algorithms(f) = new ACUnification(f)
    algorithms(f).unify(term1, term2)
  }

   def unify(f:ConstantSymbolA, terms : List[FOLTerm]) : Seq[Substitution[FOLTerm]] = {
    /* this is very inefficient */
    terms match {
      case Nil => Seq(Substitution())
      case _::Nil => Seq(Substitution())
      case x::y::rest =>
        val subst_rest      : Seq[Substitution[FOLTerm]] = unify(f, y::rest)
        val alternatives    : Seq[FOLTerm] = subst_rest map (_.apply(y))
        val possible_substs : Seq[Seq[Substitution[FOLTerm]]] = (alternatives map (unify(f,x,_)))
        val without_nonunifiables : Seq[(Substitution[FOLTerm], Seq[Substitution[FOLTerm]])] = (subst_rest zip possible_substs) filter (! _._2.isEmpty)

        /* this is nonfunctional, but probably easier to understand */
        var result : List[Substitution[FOLTerm]] = List[Substitution[FOLTerm]]()
        for ( pair <- without_nonunifiables ) {
          val sigma = pair._1
          for (tau <- pair._2)
              result = (sigma compose tau) :: result
        }

        result
    }

  }

  val debuglevel = 0 // 0... no output, 1 ... show unifiers after unification 2--- also before unification 3... maximum

  def debug(level: Int, msg: String) = if (debuglevel >= level) println("DEBUG: " + msg + " \\\\")
}

class ACUnification(val f:ConstantSymbolA) extends FinitaryUnification[FOLTerm] {
  import ACUnification.debug
  import ACUtils._
  import ListUtils._
  import MathUtils._
  import TermUtils._
  import Vector._

  type TermCount = (FOLTerm, Int)
  type ListEntry = (Int, Vector, List[Vector])
  type MapEntry = (Int, List[Vector])
  type ArrayEntry = (Vector, MapEntry)

//  var unit_constant = FOLConst(new ConstantStringSymbol("1"))

//  val is_ac1: Boolean = false

  def unify(term1:FOLTerm, term2:FOLTerm) : List[Substitution[FOLTerm]] = unify(f,term1,term2)


  def unify(function: ConstantSymbolA, term1: FOLTerm, term2: FOLTerm): List[Substitution[FOLTerm]] = {
    unify(function, List((term1, term2)), List(Substitution[FOLTerm]()))
  }

  def unify(function: ConstantSymbolA,
            terms: List[(FOLTerm, FOLTerm)],
            substs: List[Substitution[FOLTerm]]): List[Substitution[FOLTerm]] = {
    debug(3, "unifying " + terms + " substitutions are: " + substs)
    terms match {
      case (term1, term2) :: rest =>
        term1 match {
        // comparing constant to sthg else
          case FOLConst(c1) =>
            term2 match {
            // if the two constants are equal, the substitution is not changed, else not unifiable
              case FOLConst(c2) =>
                if (c1 == c2) collect(substs, ((s: Substitution[FOLTerm]) => unify(function, rest, List(s))))
                else Nil
              // second one is a var => flip & variable elimination
              case FOLVar(v) =>
                val ve = Substitution[FOLTerm](term2.asInstanceOf[FOLVar], term1)
                val newterms = rest map makesubstitute_pair(ve)
                collect(substs, (s: Substitution[FOLTerm]) => unify(function, newterms, List(ve compose s))) //TODO:check, ok
              // anything else is not unifiable
              case _ =>
                Nil
            }
          // comparing function symbol to sthg else
          case Function(f1, args1) =>
            term2 match {
            // decomposition or ac unification, if the function symbols are the same, else not unifiable
              case Function(f2, args2) =>
                if (f1 != f2) {
                  Nil
                } else if (args1.length != args2.length) {
                  throw new Exception("function symbols both named " + f1 + " but with different arity "
                          + args1.length + " and " + args2.length + "encountered!")
                } else if (f1 == function) {
                  //ac unification
                  val acunivs = ac_unify(function, term1, term2)
                  collect(acunivs, ((acu: Substitution[FOLTerm]) =>
                    collect(substs, ((subst: Substitution[FOLTerm]) =>
                      unify(function, rest map makesubstitute_pair(subst), List((acu compose subst)))) //TODO:check, ok
                      )))
                } else {
                  //non ac unification => decomposition
                  collect(substs, (s: Substitution[FOLTerm]) => unify(function, (args1 zip args2) ::: rest, List(s)))
                }
              // variable as second term: flip & variable elimination
              case FOLVar(v) =>
                //occurs check
                if (occurs(term2.asInstanceOf[FOLVar], term1)) {
                  Nil
                } else {
                  val ve = Substitution[FOLTerm](term2.asInstanceOf[FOLVar], term1)
                  val newterms = rest map makesubstitute_pair(ve)
                  collect(substs, (s: Substitution[FOLTerm]) => unify(function, newterms, List((ve compose s)))) //TODO:check, ok
                }
              // anything else is not unifiable
              case _ =>
                Nil
            }

          //variable elimination
          case FOLVar(v) =>
            term2 match {
              case FOLVar(w) =>
                if (v == w) {
                  collect(substs, (s: Substitution[FOLTerm]) => unify(function, rest, List(s)))
                } else {
                  val ve = Substitution[FOLTerm](term1.asInstanceOf[FOLVar], term2)
                  val newterms = rest map makesubstitute_pair(ve)
                  collect(substs, (s: Substitution[FOLTerm]) => unify(function, newterms, List((ve compose s).asInstanceOf[Substitution[FOLTerm]]))) //TODO:check, ok
                }

              case _ =>
                //occurs check
                if (occurs(term1.asInstanceOf[FOLVar], term2)) {
                  Nil
                } else {
                  val ve = Substitution[FOLTerm](term1.asInstanceOf[FOLVar], term2)
                  val newterms = rest map makesubstitute_pair(ve)
                  collect(substs, (s: Substitution[FOLTerm]) => unify(function, newterms, List[Substitution[FOLTerm]]((ve compose s)))) //TODO:check, ok
                }
            }

          //this should be empty in the end
          case _ =>
            throw new Exception("there should be only variables, constants and functions in first order terms!")
        }

      case Nil =>
        substs
    }
  }


  def ac_unify(function: ConstantSymbolA, term1: FOLTerm, term2: FOLTerm): List[Substitution[FOLTerm]] = {
    debug(1, "=== unifying " + flatten(function, term1) + " with " + flatten(function, term2) + "===")
    val counted_symbols = countSymbols(nestedFunctions_toList(function, term1), nestedFunctions_toList(function, term2))
    val (ts1, count1) = counted_symbols.unzip

    val (lhs, rhs) = (counted_symbols partition (_._2 > 0)) // this works because countSymbols only returns values != 0
    val vlhs = Vector(lhs map (_._2))
    val vrhs = Vector(rhs map (_._2 * -1))


    val (unifiable_invariant, unifiable_condition) = createConstantFilter((lhs map (_._1)) ::: (rhs map (_._1)))

    val vlhs_length = vlhs.length
    val vrhs_length = vrhs.length

    if ((lhs == Nil) && (rhs == Nil)) {
      List(Substitution[FOLTerm]())
    } else if ((lhs == Nil) || (rhs == Nil)) {
      Nil
    } else {
      val basis = LankfordSolver solve (vlhs, vrhs) sortWith Vector.lex_<
      //val sums  = calculateSums_new(basis, vlhs, vrhs, unifiable_invariant)
      val sums = calculateSums_new_efficient(basis, vlhs, vrhs, unifiable_invariant)
      //debug(1,"difference :"+(sums-sums2)+ " and "+(sums2-sums))

      var results: List[Vector] = Nil
      // filter vectors 
      for (v <- sums.toList) {
          if (gzero(v._1))
            results = v._1 :: results
      }

      results = results.filter(unifiable_condition)


      // remove vectors which are subsumed by smaller vectors
      results = removeSubsumedVectors_new(results, Vector(vlhs.vector ::: vrhs.vector))
      //debug(1,"number of solutions: "+results.size)

      // associate every base vector to a fresh logical variable
      val varmap = new HashMap[Vector, VariableSymbolA]

      debug(1, "basis:")
      for (b <- basis) {
        val v: VariableSymbolA = generator.getFreshVariable()
        debug(1, "$" + v + "<-" + b + "$")
        varmap(b) = v
      }

      for (s <- sums.toList.sortWith((x: (Vector, List[(Int, List[Vector])]), y: (Vector, List[(Int, List[Vector])])) => Vector.lex_<(x._1, y._1)))
        debug(1, "whole sums " + s)


      for (s <- results)
        debug(1, "sum $" + s + "$ with representative $" + sums(s).map(_._2.map(varmap(_))))
      //      debug(1,"sum $"+s+"$ with representative $"+sums(s).head._2.map(varmap(_))+"$ sum in map=$"+sums(s).head._1+"$")

      //some helper functions, could be factored out
      def extract(pair: (Int, List[Vector])): List[Vector] = pair._2

      def ntimes[A](x: A, n: Int): List[A] = if (n <= 0) Nil else x :: ntimes(x, n - 1)

      def nfilter[A](l: List[A], count: (A => Int)): List[A] = {
        l match {
          case x :: xs => ntimes(x, count(x)) ::: nfilter(xs, count)
          case Nil => Nil
        }
      }

      def createVectors(mapping: HashMap[Vector, VariableSymbolA], v: List[Vector]): List[FOLTerm] = {
        //val len = v.length
        val len = if (v == Nil) 0 else v(0).length - 1

        //println("create vectors length="+len+" v="+v)
        val expanded: List[(Int, List[Vector])] = ((0 to len) map ((_, v))).toList //pair vector with every index of a component
        val filtered: List[List[VariableSymbolA]] =
        expanded map (x =>
          (nfilter(x._2, ((v: Vector) => v.vector(x._1)))) //take the vector the number of times of the actual component
                  map (mapping(_)) //and convert them to VariableSymbols
                )
        val ltt: List[VariableSymbolA] => FOLTerm = listToTerm(function, _)
        filtered map ltt
      }

      debug(2, "" + results.length + " ac unification preresults:" + results)
      //convert results to list of terms
      var converted: List[List[FOLTerm]] = Nil
      for (r <- results) {
        for (i <- sums(r).map(extract))
        //val i = sums(r).map(extract).head //one representative is enough
          converted = createVectors(varmap, i) :: converted
      }


      debug(1, "$" + converted.length + "$ ac unification results: $" + converted + "$")

      var unified_terms: List[List[FOLTerm]] = Nil
      var unifiers: List[Substitution[FOLTerm]] = Nil
      for (c <- converted) {
        val zc = ts1 zip c
        //println("finding unifier for: "+zc)
        val us = unify(function, zc, List(Substitution[FOLTerm]()))
        for (unifier <- us) {
          val uterm: List[FOLTerm] = ts1 map ((x: FOLTerm) => unifier.apply(x))
          //println("yay found one:" + uterm)
          //unifiers = subst :: unifiers
          unifiers = unifier :: unifiers
          unified_terms = uterm :: unified_terms
        }
      }

      val term_context = (ts1 map ((x: FOLTerm) => getVariableContext(x))) reduceLeft (_ ++ _)

      //remove variables not in the original term from the substitution
      debug(2, "and the unifiers are:")
      var reduced_unifiers: List[Substitution[FOLTerm]] = Nil
      val base_variables = varmap.values.toList.map(FOLVar(_))
      for (u <- unifiers) {
        debug(2, "$" + u + "$")
        //val splitted : Tuple2[List[(FOLVar,FOLTerm)], List[(FOLVar,FOLTerm)]] = (u.mapFOL.partition(term_context contains _._1)).asInstanceOf[Tuple2[List[(FOLVar,FOLTerm)], List[(FOLVar,FOLTerm)]]]
//        val umap = (u.map.elements.toList).asInstanceOf[List[(FOLVar, FOLTerm)]]
        val umap = u.map.toList.asInstanceOf[List[(FOLVar, FOLTerm)]] 

        val in_term = umap.filter((x: (FOLVar, FOLTerm)) => (term_context contains x._1))
        debug(3, "variables in term: " + in_term)
        //apply subsitutions of z_i<-t to the rest of the substituted terms, since z_i is free
        val not_in_term = Substitution[FOLTerm](umap.filter((x: (FOLVar, FOLTerm)) => !(term_context contains x._1)))
        val in_term_reduced = in_term map ((x: (FOLVar, FOLTerm)) => (x._1, not_in_term.apply(x._2)))
        //if a variable from the original term is renamed to a base variable, switch the renaming
        var renamed = in_term_reduced
        var switch_candidates = renamed filter ((x: (FOLVar, FOLTerm)) => (base_variables contains x._2))
        while (switch_candidates.length > 0) {
          val candidate = switch_candidates.head
          val subst = Substitution[FOLTerm]((candidate._2.asInstanceOf[FOLVar]), candidate._1)
          renamed = (renamed filter (_ != candidate)) map ((x: (FOLVar, FOLTerm)) => (x._1, subst apply x._2))
          switch_candidates = renamed filter ((x: (FOLVar, FOLTerm)) => (base_variables contains x._2))
        }

        reduced_unifiers = Substitution[FOLTerm](renamed) :: reduced_unifiers
      }

      reduced_unifiers
    }
  }


  def calculateSums(basis: List[Vector], vlhs: Vector, vrhs: Vector, invariant: (Vector => Boolean)) = {
    val sums = new HashMap[Vector, List[(Int, List[Vector])]]
    var oldnewest: List[(Int, Vector, List[Vector])] = Nil
    var newest: List[(Int, Vector, List[Vector])] = Nil

    for (b <- basis) {
      val weight = vector_weight(vlhs, b)
      sums(b) = List((weight, List(b)))
      newest = (weight, b, List(b)) :: newest
    }

    val maxweight = calculateMaxWeight(vlhs, vrhs)
    debug(1, "upper bound to sum of vectors: " + maxweight)

    while (newest.size > 0) {
      oldnewest = newest
      newest = Nil

      for (v <- oldnewest) {
        val candidates = basis map (x => (vector_weight(vlhs, x) + v._1, x + v._2, x :: v._3))

        for (candidate <- candidates) {
          val (weight, sum, vectors) = candidate
          val entry: (Int, List[Vector]) = (weight, vectors sortWith Vector.lex_<)
          val newest_entry: (Int, Vector, List[Vector]) = (weight, sum, entry._2)

          if (weight <= maxweight) { //drop any sum that is too large
            if (sums.contains(sum)) {
              // if the linear combination was already generated, add it to the list
              val l: List[(Int, List[Vector])] = sums(sum)
              if (!l.contains(entry))
                sums(sum) = entry :: l
            } else {
              // else create a new entry and calculate possible new linear combinations
              sums(sum) = List(entry)
              //if (weight < maxweight && sum.anyeqzero && invariant)
              if (invariant(sum)) //TODO: check if the anyeqzero is correct, the invariant has to be true anyway
                newest = newest_entry :: newest
            }
          }
        }
      }
    }

    sums
  }

  /* this is rather inefficient, but generates fewer solutions */
  def calculateSums_new(basis: List[Vector], vlhs: Vector, vrhs: Vector, invariant: (Vector => Boolean)) = {
    val sums = new HashMap[Vector, List[(Int, List[Vector])]]
    val maxweight = calculateMaxWeight(vlhs, vrhs)
    debug(1, "upper bound to sum of vectors: " + maxweight)
    val zero = basis(0).zero
    val ps = powerset(basis)
    val pswithsums = ps map ((x: List[Vector]) => {val sum = vectorSum(x, zero); (sum, x, vector_weight(vlhs, sum))})
    var solutions = 0
    for (i <- pswithsums) {
      debug(1, "fullsum  " + i._1 + " weight=" + i._3 + " list=" + i._2)
      solutions += i._2.length
    }
    debug(1, "# of solutions " + solutions)
    val ps_inv = pswithsums filter ((x: (Vector, List[Vector], Int)) => invariant(x._1) && (x._3 <= maxweight) && (x._3 > 0))

    for (p <- ps_inv) {
      val (sum, vs, weight) = p
      if (sums contains sum) {
        val list = sums(sum)
        sums(sum) = (weight, vs) :: list
      } else {
        sums(sum) = List((weight, vs))
      }
    }
    sums
  }

  def calculateSums_new_efficient(basis: List[Vector], vlhs: Vector, vrhs: Vector, invariant: (Vector => Boolean)) = {
    val sums = new HashMap[Vector, List[(Int, List[Vector])]]
    val maxweight = calculateMaxWeight(vlhs, vrhs)
    val zero = basis(0).zero
    val invariant_ = (x: Vector) => invariant(x) && (vector_weight(vlhs, x) <= maxweight)
    val fpowerset = filterpowerset((zero, Nil: List[Vector]), basis, invariant_)
    for (s <- fpowerset) {
      val (sum, vectors) = s
      if (!sums.contains(sum)) {
        sums(sum) = List((vector_weight(vlhs, sum), vectors))
      } else {
        val entry = sums(sum)
        val new_entry = (vector_weight(vlhs, sum), vectors)
        if (!entry.contains(new_entry))
          sums(sum) = new_entry :: entry
      }
    }

    sums
  }


  def filterpowerset(in: (Vector, List[Vector]), still_left: List[Vector], invariant: (Vector => Boolean)): List[(Vector, List[Vector])] = {
    still_left match {
      case Nil => List(in)
      case _ => rflattenLists(still_left map ((x: Vector) => filterpowerset(in, dropuntil(x, still_left), invariant))) :::
              rflattenLists(still_left map ((x: Vector) => {
                val in_new = (in._1 + x, x :: in._2)
                if (invariant(in_new._1))
                  filterpowerset(in_new, dropuntil(x, still_left), invariant)
                else
                  Nil
              }))
    }
  }



  /* convert list of variable symbols to a term f(x_1,f(x_2, ...)) */
  def listToTerm(function: ConstantSymbolA, terms: List[VariableSymbolA]): FOLTerm = {
    terms match {
      case x :: Nil => FOLVar(x)
      case x :: xs => Function(function, List(FOLVar(x), listToTerm(function, xs)))
      case Nil =>
          throw new Exception("cannot convert empty list to term, there is no unit element!")
    }
  }

  def composable_by(v: Vector, vs: List[Vector]): Boolean = {
    vs match {
      case Nil => false
      case _ =>
        val reduced = (vs map (_ - v))
        if (reduced contains v.zero)
          true
        else {
          composable_by(v, reduced filter gzero)
        }
    }

  }

  def vector_weight(vlhs: Vector, v: Vector): Int = vlhs * Vector(v.vector slice (0, vlhs.length))


  def calculateMaxWeight(l: Vector, r: Vector): Int = {
    var maxab = 0
    var lcm_act = 0
    for (i <- l.vector)
      for (j <- r.vector) {
        lcm_act = lcm(i, j)
        if (lcm_act > maxab)
          maxab = lcm_act
      }
    return max(l.length, r.length) * maxab
  }


  /* counts the number of symbols, those in terms1 count positively, thos in count2 negatively */
  def countSymbols(terms1: List[FOLTerm], terms2: List[FOLTerm]): List[TermCount] = {
    var result: List[TermCount] = Nil
    for (t <- terms1) {
      result = insertTerm(t, result, 1)
    }
    for (t <- terms2) {
      result = insertTerm(t, result, -1)
    }
    result filter (_._2 != 0)
  }

  /* finds term in list and increses its counter */
  def insertTerm(term: FOLTerm, list: List[TermCount],i:Int): List[TermCount] = {
    list match {
      case Nil => List((term, i))
      case (lterm, count) :: rest =>
        if (term == lterm)
          (lterm, count + i) :: rest
        else
          (lterm, count) :: insertTerm(term, rest, i)
    }
  }


  /* creates a function that applies a given substitution to a pair of terms */
  def makesubstitute_pair(subst: Substitution[FOLTerm]): (((FOLTerm, FOLTerm)) => (FOLTerm, FOLTerm)) =
    (x: (FOLTerm, FOLTerm)) => (subst.apply(x._1), subst.apply(x._2))


  /* occurs check : true iff term contains v */
  def occurs(v: FOLVar, term: FOLTerm): Boolean = {
    term match {
      case FOLVar(w) => v == term
      case FOLConst(_) => false
      case Function(_, args) => args.foldLeft(false)(_ || occurs(v, _))
    }
  }


  /* creates a function, which checks if a vector is <= 1 at the given indices */
  def makeLTEQ1Filters(ns: List[Int]): (Vector => Boolean) = (v: Vector) =>
    (ns map (v.vector(_) <= 1)).foldLeft(true)(_ && _)

  /* creates a function, which checks if a vector is <= 1 at the given indices */
  def makeEQ1Filters(ns: List[Int]): (Vector => Boolean) = (v: Vector) =>
    (ns map (v.vector(_) == 1)).foldLeft(true)(_ && _)


  /* creates two filters that checks if the number of terms that later has to be unified with a constant or
  * function term does not exceed 1. the first function is true as long as the corresponding components are <= 1,
  * the second is true as long the corresponding components are exactly 1.
  * the first function is intended to be checked while generating solutions, the second is to be checked after
  * all solutions have been generated */
  def createConstantFilter(symbols: List[FOLTerm]): ((Vector => Boolean), (Vector => Boolean)) = {
    var i: Int = 0
    var indices: List[Int] = Nil
    for (s <- symbols) {
      s match {
        case FOLVar(_) =>; //do nothing
        case FOLConst(_) => indices = i :: indices
        case Function(_, _) => indices = i :: indices
        case _ => throw new Exception("unhandled term type " + s.getClass + " of term " + s)
      }
      i += 1
    }
    (makeLTEQ1Filters(indices), makeEQ1Filters(indices))
  }

}

object ACUtils {
  import ACUnification.debug
  import TermUtils.term_<

  def structural_fold(fun : (FOLTerm => FOLTerm), formula: FOLFormula): FOLFormula =
    formula match {
      case Atom(p, args) => Atom(p, args map ((x:FOLTerm) => fun(x)))
      case Neg(l) => Neg(structural_fold(fun,l))
      case AllVar(q,l) => AllVar(q,structural_fold(fun,l))
      case ExVar(q,l) => ExVar(q,structural_fold(fun,l))
      case And(l,r) => And(structural_fold(fun,l), structural_fold(fun,r))
      case Or(l,r)  => Or(structural_fold(fun,l), structural_fold(fun,r))
      case Imp(l,r) => Imp(structural_fold(fun,l), structural_fold(fun,r))
      case _ => throw new Exception("Unkonwn operator during structrual folding of formula!")
    }

  //performs the flattening operation below on formulas
  def flatten(f: ConstantSymbolA, formula: FOLFormula): FOLFormula = structural_fold((x:FOLTerm) => flatten(f,x), formula )

  /*
  def flatten(f: ConstantSymbolA, formula: FOLFormula): FOLFormula = {
    formula match {
      case Atom(p, args) => Atom(p, args map ((x:FOLTerm) => flatten(f,x)))
      case Neg(l) => Neg(flatten(f,l))
      case AllVar(q,l) => AllVar(q,flatten(f,l))
      case ExVar(q,l) => ExVar(q,flatten(f,l))
      case And(l,r) => And(flatten(f,l), flatten(f,r))
      case Or(l,r) => Or(flatten(f,l), flatten(f,r))
      case Imp(l,r) => Imp(flatten(f,l), flatten(f,r))
      case _ => throw new Exception("Unkonwn operator during flattening of fomrula!")
    }
  } */

  /* performs the rewrite rule f(s1, ... , f(t1, ... ,tm), ...sn) -> f(s1, ... ,t1, ... ,tm, ...sn) on the
   * given term (see also: Lincoln 89 "Adventures in Associative-Commutative Unification") and sorts the
   * the argument list lexicographically*/
  def flatten(f: ConstantSymbolA, term: FOLTerm): FOLTerm = {
    term match {
      case FOLVar(_) => term
      case FOLConst(_) => term
      case Function(fun, args) =>
        if (f == fun) {
          Function(fun, ((args map ((x: FOLTerm) => stripFunctionSymbol(f, x))).reduceRight(_ ::: _)
                            map ((x: FOLTerm) => flatten(f, x))) sortWith term_<)
        } else {
          Function(fun, args map ((x: FOLTerm) => flatten(f, x)))
        }
    }
  }

  /* flatten but removes the neutral element, i.e. f(x) = x, f() = e*/
  def flatten_andfiltersymbol(f: ConstantSymbolA, e:ConstantSymbolA, formula: FOLFormula): FOLFormula =
    structural_fold((x:FOLTerm) => flatten_andfiltersymbol(f,e,x), formula )

  def flatten_andfiltersymbol(f: ConstantSymbolA, e:ConstantSymbolA, term: FOLTerm): FOLTerm =
    sortargsof_in(f, flatten_andfiltersymbol_withoutsorting(f,e,term)  )

  def flatten_andfiltersymbol_withoutsorting(f: ConstantSymbolA, e:ConstantSymbolA, term: FOLTerm): FOLTerm = {
    term match {
      case FOLVar(_) => term
      case FOLConst(_) => term
      case Function(fun, args) =>
        if (f == fun) {
          val c = FOLConst(e)
          val args_ = (((args map ((x: FOLTerm) => stripFunctionSymbol(f, x))).reduceRight(_ ::: _) map
                        ((x: FOLTerm) => flatten_andfiltersymbol_withoutsorting(f, e, x)))
                       sortWith term_<) filterNot (_ == c)

          args_ match {
            case Nil => FOLConst(e)
            case List(t) => t
            case _ => Function(fun,args_)
          }
        } else {
          Function(fun, args map ((x: FOLTerm) => flatten_andfiltersymbol_withoutsorting (f, e, x)))
        }
    }
  }

  def sortargsof_in(f : ConstantSymbolA, t : FOLTerm) : FOLTerm = t match {
    case Function(sym, args) =>
      val args_ = args map (sortargsof_in(f,_))
      if (f == sym)
        Function(sym, args_ sortWith term_< )
      else
        Function(sym, args_)
    case _ => t
  }

  def sortargsof_in(fs : List[ConstantSymbolA], t : FOLTerm) : FOLTerm = t match {
    case Function(sym, args) =>
      val args_ = args map (sortargsof_in(fs,_))
      if (fs contains sym)
        Function(sym, args_ sortWith term_< )
      else
        Function(sym, args_)
    case _ => t
  }


  /* removes the nesting of f in a term to a list - since the term f(g(f(x,y),z) should rewrite to
   * f(x,y,z) instead of f(f(x,y),z), it is preferred to use flatten */
  def stripFunctionSymbol(f: ConstantSymbolA, term: FOLTerm): List[FOLTerm] = {
    term match {
      case Function(fun, args) =>
        if (f == fun)
          (args map ((x: FOLTerm) => stripFunctionSymbol(f, x))).reduceRight(_ ::: _)
        else
          List(term)
      case _ => List(term)
    }
  }

  //TODO: refactor
  def nestedFunctions_toList(function: ConstantSymbolA, term: FOLTerm): List[FOLTerm] = {
    term match {
      case v: FOLVar => List(v)
      //case c : FOLConst => List(c)
      case Function(name, args) =>
        if (name == function) {
          val join = ((x: List[FOLTerm], y: List[FOLTerm]) => x ++ y)
          args.map(nestedFunctions_toList(function, _)) reduceLeft join
        } else {
          List(Function(name, args))
        }
      case _ =>
        Nil
    }
  }

  def removeSubsumedVectors_new(arg: List[Vector], weight: Vector): List[Vector] = {
    var removed: List[Vector] = Nil
    val sortedarg = arg sortWith (_ * weight < _ * weight)
    debug(1, "sorted list by " + weight + " is " + sortedarg)
    for (v <- sortedarg) {
      if (!linearlydependent_on(v, removed)) {
        removed = v :: removed
        debug(1, "adding " + v + " to result list")
      } else {
        debug(1, "throwing away " + v)
      }

    }
    removed
  }

  def linearlydependent_on(v: Vector, list: List[Vector]): Boolean = {
    var changed = true
    var vs: List[Vector] = List(v)
    while (changed) {
      changed = false
      var newones: List[Vector] = Nil
      for (i <- vs)
        newones = newones ::: (list map (i - _))
      debug(4, "newones=" + newones)
      if (newones contains v.zero) {
        debug(4, "" + v + " is linearly dependent on " + list)
        return true
      }

      val newonesgz = newones filter Vector.geqzero
      if (newonesgz.length > 0) {
        changed = true
        vs = newonesgz
        debug(3, ("v=" + v + " vs=" + vs))
      }
    }

    return false
  }
  
}

class ACUEquality(val function_symbol : ConstantSymbolA, val zero_symbol : ConstantSymbolA) extends EequalityA {
  import ACUtils.flatten
  private class Parser(input : String) extends StringReader(input) with SimpleFOLParser
  private def parse(s:String) = (new Parser(s)).formula.asInstanceOf[FOLTerm]

  private val zero = FOLConst(zero_symbol)
  private def f(s:FOLTerm, t:FOLTerm) = Function(function_symbol, List(s,t))

  override def equational_rules() : Set[Equation] = {
    val x = FOLVar(new VariableStringSymbol("x"))
    val y = FOLVar(new VariableStringSymbol("y"))
    val z = FOLVar(new VariableStringSymbol("z"))

    val assoc = Equation( f(x, f(y,z)), f(f(x,y),z))
    val comm  = Equation( f(x, y), f(y, x))
    val unit  = Equation( f(x, zero), x)

    Set(assoc, comm, unit)
  }

  override def word_equalsto(s : FOLTerm, t : FOLTerm) : Boolean = {
    (flatten (function_symbol, s)) syntaxEquals (flatten (function_symbol, t))
  }

  //todo: implementation
  override def unifies_with(s : FOLTerm, t : FOLTerm) : Option[Substitution[FOLTerm]] = None
}

class MulACEquality(val function_symbols : List[ConstantSymbolA]) extends EequalityA {
  import ACUEquality._
  def f(sym:ConstantSymbolA, x:FOLTerm, y:FOLTerm) = Function(sym,List(x,y))

  def flatten(f : FOLFormula) = function_symbols.foldLeft(f)( (formula : FOLFormula, sym:ConstantSymbolA) => ACUtils.flatten(sym, formula)  )

  override def equational_rules() : Set[Equation] = {
    val x = FOLVar(new VariableStringSymbol("x"))
    val y = FOLVar(new VariableStringSymbol("y"))
    val z = FOLVar(new VariableStringSymbol("z"))

    val assoc = function_symbols map( fs => Equation( f(fs,x, f(fs,y,z)), f(fs,f(fs,x,y),z)))
    val comm  = function_symbols map( fs => Equation( f(fs, x, y), f(fs, y, x)) )

    (assoc ++ comm) toSet
  }


  override def word_equalsto(s:FOLTerm, t:FOLTerm) : Boolean =  fold_flatten(function_symbols,s) syntaxEquals fold_flatten(function_symbols,t)

  //todo: implementation
  override def unifies_with(s : FOLTerm, t : FOLTerm) : Option[Substitution[FOLTerm]] = None
}

class MulACUEquality(override val function_symbols : List[ConstantSymbolA], val zero_symbols : List[ConstantSymbolA]) extends MulACEquality(function_symbols) {
  require { function_symbols.length == zero_symbols.length }
  import ACUEquality._

  val fzsymbols = function_symbols zip zero_symbols

  override def equational_rules() : Set[Equation] = {
    val x = FOLVar(new VariableStringSymbol("x"))

    val acrules : Set[Equation] = super.equational_rules()
    val urules = fzsymbols map ((i : (ConstantSymbolA, ConstantSymbolA)) => { Equation( f(i._1, x, FOLConst(i._2)), x)  })
    acrules ++ urules.toSet
  }

  override def flatten(f : FOLFormula) = fzsymbols.foldLeft(f)( (formula : FOLFormula, sym:(ConstantSymbolA, ConstantSymbolA)) => ACUtils.flatten_andfiltersymbol(sym._1, sym._2, formula)  )

  override def word_equalsto(s:FOLTerm, t:FOLTerm) : Boolean = fold_flatten_filter(function_symbols, zero_symbols, s) syntaxEquals fold_flatten_filter(function_symbols, zero_symbols, t)

  //todo: implementation
  override def unifies_with(s : FOLTerm, t : FOLTerm) : Option[Substitution[FOLTerm]] = None


}


object ACUEquality {
  import ACUtils.{flatten, flatten_andfiltersymbol_withoutsorting, sortargsof_in}

  def fold_flatten(fs : List[ConstantSymbolA], s:FOLTerm) = fs.foldLeft(s)( (term : FOLTerm, f : ConstantSymbolA) => flatten(f, term) )

  def fold_flatten_filter(fs : List[ConstantSymbolA], cs : List[ConstantSymbolA], s:FOLTerm) : FOLTerm =
    sortargsof_in(fs, (fs zip cs).foldLeft(s)(
      (term : FOLTerm, el : ( ConstantSymbolA, ConstantSymbolA) ) => flatten_andfiltersymbol_withoutsorting(el._1, el._2, term) )
    )


  def factor_clause(e : EequalityA, clause : FSequent) : FSequent = {
    var antecedent : Seq[FOLFormula] = clause._1.asInstanceOf[Seq[FOLFormula]]
    var succedent  : Seq[FOLFormula] = clause._2.asInstanceOf[Seq[FOLFormula]]

    var ant : Seq[FOLFormula] = Nil
    while (antecedent.nonEmpty ) {
      ant = ant.+:(antecedent.head)
      antecedent = antecedent filterNot ((g:FOLFormula) => e.reequal_to(antecedent head,g))

    }

    var succ : Seq[FOLFormula] = Nil
    while (succedent.nonEmpty ) {
      succ = succ.+:(succedent.head)
      succedent = succedent filterNot ((g:FOLFormula) => e.reequal_to(succedent head,g))
    }

    FSequent(ant, succ)
  }

  def tautology_removal(theory : EequalityA, clauses : List[FSequent]) : List[FSequent] = {
    clauses.foldLeft (List[FSequent]()) ( (done : List[FSequent], s : FSequent) =>
      if (s._1.exists( (pos : HOLFormula) => s._2.exists( (neg : HOLFormula) =>  theory.reequal_to(pos.asInstanceOf[FOLFormula], neg.asInstanceOf[FOLFormula]) )))
        done
      else
        done.+:(s)

    )
  }

  //private because this only works on factorized formulas
  private def clause_restricted_subsumed_in(theory : EequalityA, clause : FSequent, list : List[FSequent]) = list.exists( (s : FSequent) =>
    clause._1.length == s._1.length &&
    clause._2.length == s._2.length &&
    clause._1.forall((f:HOLFormula) => s._1.exists((g:HOLFormula) => theory.reequal_to(f.asInstanceOf[FOLFormula], g.asInstanceOf[FOLFormula]) )) &&
    clause._2.forall((f:HOLFormula) => s._2.exists((g:HOLFormula) => theory.reequal_to(f.asInstanceOf[FOLFormula], g.asInstanceOf[FOLFormula]) ))
  )

  //returns true if clause is reequal some element of list modulo the theory, where clause may be weakened (i.e. have additional literals)
  def clause_restricted_subsumed_in2(theory : EequalityA, clause : FSequent, list : List[FSequent]) = list.exists( (s : FSequent) =>
    ( {println("looking at: "+clause + " in "+list.size); true}) &&
    s._1.forall((f:HOLFormula) => clause._1.exists((g:HOLFormula) => theory.reequal_to(f.asInstanceOf[FOLFormula], g.asInstanceOf[FOLFormula]) )) &&
    s._2.forall((f:HOLFormula) => clause._2.exists((g:HOLFormula) => theory.reequal_to(f.asInstanceOf[FOLFormula], g.asInstanceOf[FOLFormula]) )) &&
    ( {println("yes!"); true})
  )

  def restricted_subsumption(theory : EequalityA, clauses : List[FSequent]) : List[FSequent] = restricted_subsumption_(theory, Nil, clauses)

  private def restricted_subsumption_(theory : EequalityA, clauses : List[FSequent], remaining : List[FSequent]) : List[FSequent] = {
    remaining match {
      case x::xs => if (clause_restricted_subsumed_in2(theory, x, clauses))
          restricted_subsumption_(theory, clauses, xs)
        else
          restricted_subsumption_(theory, clauses.+:(x), xs)

      case Nil=> clauses
    }

  }




}


