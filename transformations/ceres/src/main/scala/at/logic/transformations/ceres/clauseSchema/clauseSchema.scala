package at.logic.transformations.ceres.clauseSchema

import at.logic.algorithms.lk.getAncestors
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types.FSequent
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.calculi.lk.macroRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.calculi.resolution.robinson.Clause
import at.logic.calculi.slk._
import at.logic.calculi.slk.AndEquivalenceRule1._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.hol.{HOLExpression, HOLFormula}
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression, Var}
import at.logic.language.schema._
import at.logic.transformations.ceres.projections.printSchemaProof
import at.logic.transformations.ceres.unfolding.{StepMinusOne, SchemaSubstitution1}
import at.logic.utils.ds.trees.LeafTree
import collection.immutable
import at.logic.parsing.language.simple.SHLK

abstract class sClause {
  override def toString: String
}


class sClauseVar(val name:String) extends sClause {
  override def toString = {name}
}

object sClauseVar {
  def apply(name:String): sClause = new sClauseVar(name)
  def unaply(s : sClause) = s match {
    case v:sClauseVar => Some(v.name)
    case _ => None
  }
}


class nonVarSclause(val ant: List[HOLFormula], val succ: List[HOLFormula]) extends sClause {
  override def toString = {
    printSchemaProof.sequentToString(Sequent(ant.map(f => defaultFormulaOccurrenceFactory.createFormulaOccurrence(f, List())), succ.map(f => defaultFormulaOccurrenceFactory.createFormulaOccurrence(f, List()))))
//    ant + " |- " + succ
  }
}

object nonVarSclause {
  def apply(ant1: List[HOLFormula], succ1: List[HOLFormula]): nonVarSclause = {
    new nonVarSclause(ant1, succ1)
  }
  def unapply(c: sClause) = c match {
    case non:nonVarSclause => Some(non.ant, non.succ)
    case _ => None
  }
}


class sClauseComposition(val sclause1: sClause, val sclause2: sClause) extends sClause {
//  override def toString = {sclause1 + " • " + sclause2}
  override def toString = {sclause1 + Console.BLUE+" ◦ " + Console.RESET+ sclause2}
}

//makes it with only one  "|-" sign
object normalizeSClause {
  def apply(c: sClause): sClause = {
    val mergeNonVarSClauses = {
      val res = getNonVarSclauses(c)
      if(res.length < 2)
      res
      else
      res.tail.foldLeft(res.head)((acc, clause) => nonVarSclause(acc.asInstanceOf[nonVarSclause].ant ++ clause.asInstanceOf[nonVarSclause].ant, acc.asInstanceOf[nonVarSclause].succ ++ clause.asInstanceOf[nonVarSclause].succ)).asInstanceOf[sClause]
    }
    val sClauseVars = getSClausVars(c)
    if(sClauseVars.isEmpty)
      return mergeNonVarSClauses.asInstanceOf[nonVarSclause]
    sClauseVars.foldLeft(mergeNonVarSClauses.asInstanceOf[sClause])((acc, v) => sClauseComposition(acc, v)).asInstanceOf[sClauseComposition]
  }
  def getNonVarSclauses(c: sClause): List[sClause] = c match {
    case v:sClauseVar => List.empty[sClause]
    case non:nonVarSclause => non::Nil
    case comp:sClauseComposition =>
      getNonVarSclauses(comp.sclause1) ++ getNonVarSclauses(comp.sclause2)
  }

  def getSClausVars(c: sClause): List[sClause] = c match {
    case v:sClauseVar => v::Nil
    case non:nonVarSclause => List.empty[sClause]
    case comp:sClauseComposition =>
      getSClausVars(comp.sclause1) ++ getSClausVars(comp.sclause2)
  }
}

object sClauseComposition {
  def apply(scl1: sClause , scl2: sClause): sClause = new sClauseComposition(scl1, scl2)
  def unaply(s: sClause) = s match {
    case compos:sClauseComposition => Some(Pair(compos.sclause1, compos.sclause2))
    case _ => None
  }
}


//replace the clause variable "v" with the corresponging clause from the Map
object replace {
  def apply(v: sClauseVar, pair: Pair[sClauseVar, sClause]): sClause = {
    if (v.name == pair._1.name)
      pair._2
    else
      v
  }
  def apply(c: sClause, varList: Map[sClauseVar, sClause]): sClause = c match {
    case v:sClauseVar if varList.keySet.contains(v) => varList.get(v).get
    case v:sClauseVar if !varList.keySet.contains(v) => throw new Exception("\nERROR 112\n!")
    case non:nonVarSclause => c
    case comp:sClauseComposition =>
      sClauseComposition(apply(comp.sclause1, varList), apply(comp.sclause2, varList))
  }
}


//the substitution is applied only to indexed predicates with index "k"
object applySubToSclause {
  def apply(sub: SchemaSubstitution1[HOLExpression], c: sClause): sClause = c match {
    case v:sClauseVar => c
    case non:nonVarSclause => {
      val ant1 = non.ant.map(f => sub(f).asInstanceOf[HOLFormula])
      val succ1 = non.succ.map(f => sub(f).asInstanceOf[HOLFormula])
      nonVarSclause(ant1, succ1)
    }
    case compos:sClauseComposition => {
      sClauseComposition(apply(sub, compos.sclause1), apply(sub, compos.sclause2))
    }
    case _ => throw new Exception("\nERROR in applySubToSclause ! \n")
  }
}


//
class ClauseSchema(val base: sClause, val rec: sClause) {
  def apply(a: IntegerTerm, varListBase: Map[sClauseVar, sClause], varListRec: Map[sClauseVar, sClause], c: sClause): sClause = {
    a match {
      case IntZero() => replace(base, varListBase)
      case    _      => {
        println("\nClauseSchema rec:")
        val k = IntVar(new VariableStringSymbol("k"))
        val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(k, a)
        val new_subst = new SchemaSubstitution1(new_map)
        val ground_c = applySubToSclause(new_subst, c)
        val new_val = apply(Pred(a), varListBase, varListRec, c)
        val Xmap = Map[sClauseVar, sClause]() + Pair(varListBase.head._1.asInstanceOf[sClauseVar], new_val)
        replace(ground_c, Xmap)
      }
    }
  }
  def apply(k: IntegerTerm, varListBase: Map[sClauseVar, sClause]): sClause = {
    val varListRec = Map[sClauseVar, sClause]() + Pair(varListBase.head._1.asInstanceOf[sClauseVar], rec)
    apply(k, varListBase, varListRec, rec)
  }
}

object ClauseSchema {
  def apply(b: sClause, r: sClause) = new ClauseSchema(b, r)
}
