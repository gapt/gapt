/*
 * MatchingAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.matching

import at.logic.syntax.language.fol._

object MatchingAlgorithm
{
  def termMatch(t1: FOLTerm, t2: FOLTerm): Option[Substitution] = (t1,t2) match
  {
    case (FOLVar(name1: VariableSymbolA, dbInd1),FOLVar(name2: VariableSymbolA, dbInd2) if name1==name2 =>
        Some(Substitution())

    case (FOLVar(name1: VariableSymbolA, dbInd1),FOLVar(name2: VariableSymbolA, dbInd2) if name1!=name2 =>
        Some(Substitution(t1,t2))

    case (FOLConst(sym1),FOLConst(sym2)) if sym1==sym2 =>
        Some(Substitution())

    case (FOLConst(sym1),FOLConst(sym2)) if sym1!=sym2 =>
        None

    case 


  }

  def match(f1: Formula, f2: Formula): Option[Substitution] = (f1,f2) match
  {
    case (Atom(sym1,args1),Atom(sym2,args2)) if sym1 == sym2 =>
      {

      }



    
  }
}
