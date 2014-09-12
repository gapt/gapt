package at.logic.algorithms.resolution

import at.logic.language.fol.{FOLVar, FOLFormula, And => FAnd, Imp => FImp, Or => FOr, Neg => FNeg, AllVar => FAllVar, ExVar => FExVar, Atom => FAtom}
import at.logic.language.hol._
import at.logic.calculi.resolution.FClause
import at.logic.language.lambda.symbols.{StringSymbol, SymbolA}
import at.logic.language.lambda.types.To
import at.logic.utils.logging.Logger

import scala.collection.mutable

/**
 * * Formulas must be regular and weakly quantified
 * (see Issue 196)
 */

  /**
   * computes the set CNF^+
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
   * computes the set CNF^-
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

object TseitinCNF extends Logger {

  var subformulaMap : mutable.HashMap[FOLFormula, FOLFormula] = new mutable.HashMap[FOLFormula, FOLFormula]()

  val hc = StringSymbol("Σ")
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

  /**
   * Generates from a formula f a Set of FClauses in CNF by using Tseitin's Transformation
   * @param f formula which should be transformed
   * @return tuple where 1st are clauses equivalent to f in CNF and Tseitin transformed f
   */
  def apply(f: FOLFormula): (Set[FClause],FOLFormula) = {
    // take an arbitrary atom symbol and rename it
    // s.t. it does not occure anywhere in f
    fsyms = getAtomSymbols(f)
    
    
    // parseFormula and transform it via Tseitin-Transformation
    val pf = parseFormula(f)

    val tseitinF = FAnd(pf._1, pf._2)
    trace("Tseitin transformed formula: "+tseitinF)

    // call distributive CNFp to transform the Tseitin-transformed
    // formula to a set of clauses
    (CNFp(tseitinF),tseitinF)
    //CNFp(tseitinF)
  }

  /**
   * Adds a FOLFormula to fol.Atom map to the subFormulas HashMap, iff
   * the subformula does not already map to an existing atom.
   * The representing atom is returned.
   * In case f is an atom itself, nothing will be added to the subformulas HashMap and the atom itself is return as 1st/2nd
   * @param f subformula to be eventually added to subformulas HashMap
   * @return an atom either representing the subformula or f if f is already an atom
   */
  def addIfNotExists(f: FOLFormula): FOLFormula = f match {
    case Atom(h,args) => f
    case _ => {
        if (subformulaMap.exists(_._1 == f)) {
          return subformulaMap(f)
        }
        else {
          // generate new atomsymbol
          val sym = at.logic.language.lambda.rename(hc, fsyms ::: auxsyms.toList)
          val auxAtom = at.logic.language.fol.Atom(sym, Nil)
          auxsyms += sym
          subformulaMap(f) = auxAtom
          return auxAtom
        }
    }
  }


  //TODO: No full FOL support => no ExVar, AllVar skolemization implemented yet
  /**
   * Takes a HOLFormula and parses it s.t. every subformula gets
   * assigned a freshly introduced Atom which is from there on used instead of the formula
   * @param f
   * @return a Tuple2, where 1st is the prop. variable representing the formula in 2nd
   */
  def parseFormula(f: FOLFormula): Tuple2[FOLFormula,FOLFormula] = {

    // eventually freshly introduced variable
    // or if subformula had been parsed already
    // the prop. var. for the subformula
    val auxVar = addIfNotExists(f)

    f match {
      case FAtom(_, _) => (f,f)
      case FNeg(f2) => {
        val pf2 = parseFormula(f2)
        // if atom and formula are equal => f2 is a leaf (atom) and shall not be abbreviated
        if(pf2._1 == pf2._2)
          (auxVar, FAnd(FImp(auxVar, f), FImp(f, auxVar)))
        else
          (auxVar, FAnd(FAnd(FImp(auxVar, f), FImp(f, auxVar)), pf2._2))
      }
      case FAnd(f1, f2) => {
        val pf1 = parseFormula(f1)
        val pf2 = parseFormula(f2)

        // if atoms and formulas are equal => f1 and f2 are leafs (atoms) and shall not be abbreviated
        if(pf1._1 == pf1._2 && pf2._1 == pf2._2)
          (auxVar, FAnd(FImp(auxVar, f), FImp(f, auxVar)))
        // if at least one of f1 and f2 are no atoms add further abbreviated subformulas
        else {
          val thisCon = FAnd(pf1._1, pf2._1)
          var newf = FAnd(FImp(auxVar, thisCon), FImp(thisCon, auxVar))
          // don't forget to take the equivalences of underlying subformulas with you
          if(pf1._1 != pf1._2){
            newf = FAnd(newf, pf1._2)
          }
          if(pf2._1 != pf2._2){
            newf = FAnd(newf, pf2._2)
          }
          (auxVar, newf)
        }
      }
      case FOr(f1, f2) => {
        val pf1 = parseFormula(f1)
        val pf2 = parseFormula(f2)
        // if atoms and formulas are equal => f1 and f2 are leafs (atoms) and shall not be abbreviated
        if(pf1._1 == pf1._2 && pf2._1 == pf2._2)
          (auxVar, FAnd(FImp(auxVar, f), FImp(f, auxVar)))
        // if at least one of f1 and f2 are no atoms add further abbreviated subformulas
        else {
          val thisCon = FOr(pf1._1, pf2._1)
          var newf = FAnd(FImp(auxVar, thisCon), FImp(thisCon, auxVar))
          // don't forget to take the equivalences of underlying subformulas with you
          if(pf1._1 != pf1._2){
            newf = FAnd(newf, pf1._2)
          }
          if(pf2._1 != pf2._2){
            newf = FAnd(newf, pf2._2)
          }
          (auxVar, newf)
        }
      }
      case FImp(f1, f2) => {
        val pf1 = parseFormula(f1)
        val pf2 = parseFormula(f2)
        // if atoms and formulas are equal => f1 and f2 are leafs (atoms) and shall not be abbreviated
        if(pf1._1 == pf1._2 && pf2._1 == pf2._2)
          (auxVar, FAnd(FImp(auxVar, f), FImp(f, auxVar)))
        // if at least one of f1 and f2 are no atoms add furhter abbreviated subformulas
        else {
          val thisCon = FImp(pf1._1, pf2._1)
          var newf = FAnd(FImp(auxVar, thisCon), FImp(thisCon, auxVar))
          // don't forget to take the equivalences of underlying subformulas with you
          if(pf1._1 != pf1._2){
            newf = FAnd(newf, pf1._2)
          }
          if(pf2._1 != pf2._2){
            newf = FAnd(newf, pf2._2)
          }
          (auxVar, newf)
        }
      }
      case _ => throw new IllegalArgumentException("unknown head of formula: " + f.toString)
    }
  }
}
