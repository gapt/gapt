package at.logic.algorithms.resolution

import at.logic.language.fol.{FOLFormula, And => FAnd, Imp => FImp, Or => FOr, Neg => FNeg, AllVar => FAllVar, ExVar => FExVar, Atom => FAtom}
import at.logic.language.hol._
import at.logic.calculi.resolution.FClause
import at.logic.language.lambda.symbols.{StringSymbol, SymbolA}

import scala.collection.mutable

/**
 * * Formulas must be regular and weakly quantified
 * (see Issue 196)
 */

  /**
   * computes the set CNF^+^
   */
  object CNFp {
    def apply(f: HOLFormula): Set[FClause] = f match {
      case Atom(_,_) => Set(FClause(List(), List(f)))
      case Neg(f2) => CNFn(f2)
      case And(f1,f2) => CNFp(f1) union CNFp(f2)
      case Or(f1,f2) => times(CNFp(f1),CNFp(f2))
      case Imp(f1,f2) => times(CNFn(f1),CNFp(f2))
      case AllVar(_,f2) => CNFp(f2)
      case _ => throw new IllegalArgumentException("unknown head of formula: " + f.toString)
    }
  }

  /**
   * computes the set CNF^-^
   */
  object CNFn {
    def apply(f: HOLFormula): Set[FClause] = f match {
      case Atom(_,_) => Set(FClause(List(f), List()))
      case Neg(f2) => CNFp(f2)
      case And(f1,f2) => times(CNFn(f1),CNFn(f2))
      case Or(f1,f2) => CNFn(f1) union CNFn(f2)
      case Imp(f1,f2) => CNFp(f1) union CNFn(f2)
      case ExVar(_,f2) => CNFn(f2)
      case _ => throw new IllegalArgumentException("unknown head of formula: " + f.toString)
    }
  }

  object times {
    def apply(s1: Set[FClause], s2: Set[FClause]): Set[FClause] = {
      s1.flatMap(c1 => s2.map(c2 => c1 compose c2))
    }
  }

object TseitinCNF {
  /**
   * Generates from a formula f a Set of FClauses in CNF by using Tseitin's Transformation
   * @param f formula which should be transformed
   * @param tseitinInstance a previously called TseitinCNF instance, which provides dependencies for future computations
   * @return triple where 1st are clauses equivalent to f in CNF, 2nd is the subformulaMap and 3rd is an atomBlacklist for eventual further TseitinCNF computations
   */
  def apply(f: FOLFormula, tseitinInstance: TseitinCNF = null): (Set[FClause], TseitinCNF) = {

    val tseitin = tseitinInstance match {
      case null => new TseitinCNF()
      case _ => {
        val t = new TseitinCNF()
        t.subformulaMap ++= tseitinInstance.subformulaMap
        t.auxsyms ++= tseitinInstance.auxsyms
        t.fsyms ++= tseitinInstance.fsyms
        t
      }
    }

    (tseitin.transform(f), tseitin)
  }
}

class TseitinCNF {

  // add already known subformulas
  val subformulaMap = mutable.Map[FOLFormula, FOLFormula]()

  val hc = StringSymbol("x")
  var fsyms = List[SymbolA]()
  var auxsyms = mutable.MutableList[SymbolA]()
  /**
   * Get a list of all Atoms symbols used in f
   * @param f formula
   * @return List of all atom symbols used in f
   */
  def getAtomSymbols(f: FOLFormula) : List[SymbolA] = f match {
    case FAtom(h,args) => List(h)
    case FNeg(f2)      => getAtomSymbols(f2)
    case FAnd(f1,f2)   => getAtomSymbols(f1) ::: getAtomSymbols(f2)
    case FOr(f1,f2)    => getAtomSymbols(f1) ::: getAtomSymbols(f2)
    case FImp(f1,f2)   => getAtomSymbols(f1) ::: getAtomSymbols(f2)
    case FExVar(_,f2)  => getAtomSymbols(f2)
    case FAllVar(_,f2) => getAtomSymbols(f2)
    case _ => throw new IllegalArgumentException("unknown head of formula: " + f.toString)
  }

  def transform(f: FOLFormula) : Set[FClause]= {
    // take an arbitrary atom symbol and rename it
    // s.t. it does not occur anywhere in f
    fsyms = getAtomSymbols(f)

    // parseFormula and transform it via Tseitin-Transformation
    val pf = parseFormula(f)
    pf._2 + FClause(List(), List(pf._1))
  }

  /**
   * Adds a FOLFormula to fol.Atom map to the subFormulas HashMap, iff
   * the subformula does not already map to an existing atom.
   * The representing atom is returned.
   * In case f is an atom itself, nothing will be added to the subformulas HashMap and the atom itself is return as 1st/2nd
   * @param f subformula to possibly be added to subformulas HashMap
   * @return an atom either representing the subformula or f if f is already an atom
   */
  def addIfNotExists(f: FOLFormula): FOLFormula = f match {
    case Atom(h,args) => f
    case _ =>
      if (subformulaMap.isDefinedAt(f)) {
        subformulaMap(f)
      }
      else {
        // generate new atom symbol
        val sym = at.logic.language.lambda.rename(hc, fsyms ::: auxsyms.toList)
        val auxAtom = FAtom(sym, Nil)
        auxsyms += sym
        subformulaMap(f) = auxAtom
        auxAtom
      }
  }

  /**
   * Takes a propositional FOLFormula and parses it s.t. every subformula gets
   * assigned a freshly introduced Atom which is from there on used instead of the formula
   * @param f The formula to be parsed.
   * @return a Tuple2, where 1st is the prop. variable representing the formula in 2nd
   */
  def parseFormula(f: FOLFormula): Tuple2[FOLFormula,Set[FClause]] = f match {
    case FAtom(_, _) => (f, Set())

    case FNeg(f2) =>
      val pf = parseFormula(f2)
      val x = addIfNotExists(f)
      val x1 = pf._1
      val c1 = FClause(List(x, x1), List())
      val c2 = FClause(List(), List(x, x1))
      (x, pf._2 ++ Set(c1, c2))

    case FAnd(f1, f2) =>
      val pf1 = parseFormula(f1)
      val pf2 = parseFormula(f2)
      val x = addIfNotExists(f)
      val x1 = pf1._1
      val x2 = pf2._1
      val c1 = FClause(List(x), List(x1))
      val c2 = FClause(List(x), List(x2))
      val c3 = FClause(List(x1, x2), List(x))
      (x, pf1._2 ++ pf2._2 ++ Set(c1, c2, c3))

    case FOr(f1, f2) =>
      val pf1 = parseFormula(f1)
      val pf2 = parseFormula(f2)
      val x = addIfNotExists(f)
      val x1 = pf1._1
      val x2 = pf2._1
      val c1 = FClause(List(x1), List(x))
      val c2 = FClause(List(x2), List(x))
      val c3 = FClause(List(x), List(x1, x2))
      (x, pf1._2 ++ pf2._2 ++ Set(c1, c2, c3))

    case FImp(f1, f2) =>
      val pf1 = parseFormula(f1)
      val pf2 = parseFormula(f2)
      val x = addIfNotExists(f)
      val x1 = pf1._1
      val x2 = pf2._1
      val c1 = FClause(List(), List(x, x1))
      val c2 = FClause(List(x2), List(x))
      val c3 = FClause(List(x, x1), List(x2))
      (x, pf1._2 ++ pf2._2 ++ Set(c1, c2, c3))

    case _ => throw new IllegalArgumentException("Formula not supported in Tseitin transformation: " + f.toString)
  }
}
