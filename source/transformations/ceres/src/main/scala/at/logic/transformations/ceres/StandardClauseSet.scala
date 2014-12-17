/*
 * StandardClauseSet.scala
 *
 */

package at.logic.transformations.ceres.clauseSets

import at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithmHOL
import at.logic.transformations.ceres.struct._
import at.logic.calculi.lk.base._
import at.logic.calculi.lksk._
import at.logic.calculi.occurrences._
import at.logic.language.schema.IndexedPredicate
import at.logic.language.lambda.types.{To, Tindex}
import at.logic.language.hol.{HOLExpression, HOLApp, HOLConst, HOLFormula}
import at.logic.utils.logging.Logger
import scala.annotation.tailrec
import scala.util.control.TailCalls._


object SimpleStandardClauseSet extends AlternativeStandardClauseSet( (x,y) => (x,y) )
object AlternativeStandardClauseSet extends AlternativeStandardClauseSet(
  (set1, set2) => {
    val set1_ = set1.filterNot(s1 => set2.exists(s2 => StillmanSubsumptionAlgorithmHOL.subsumes(s2, s1)))
    val set2_ = set2.filterNot(s2 => set1_.exists(s1 => StillmanSubsumptionAlgorithmHOL.subsumes(s1, s2)))
    //println("Set1: "+set1.size+" - "+(set1.size-set1_.size))
    //println("Set2: "+set2.size+" - "+(set2.size-set2_.size))
    (set1_,set2_)
  }

)

/**
 * Should calculate the same clause set as [[StandardClauseSet]], but without the intermediate representation of a
 * normalized struct.
 */
class AlternativeStandardClauseSet(val optimize_plus : (Set[FSequent], Set[FSequent]) => (Set[FSequent], Set[FSequent]) ) {
  def apply(struct:Struct) : Set[FSequent] = struct match {
    case A(fo) => Set(FSequent(Nil, List(fo.formula)))
    case Dual(A(fo)) => Set(FSequent(List(fo.formula), Nil))
    case EmptyPlusJunction() => Set()
    case EmptyTimesJunction() => Set(FSequent(Nil,Nil))
    case Plus(EmptyPlusJunction(), x) => apply(x)
    case Plus(x, EmptyPlusJunction()) => apply(x)
    case Plus(A(f1), Dual(A(f2))) if f1.formula == f2.formula =>
      Set()
    case Plus(Dual(A(f2)), A(f1)) if f1.formula == f2.formula =>
      Set()
    case Plus(x,y) =>
      val (x_, y_) = optimize_plus(apply(x), apply(y))
      x_ ++ y_
    case Times(EmptyTimesJunction(), x, _) => apply(x)
    case Times(x, EmptyTimesJunction(), _) => apply(x)
    case Times(x,y, _) =>
      val xs = apply(x)
      val ys = apply(y)
      xs.flatMap(x1 => ys.flatMap(y1 => Set(delta_compose(x1,  y1))))
    case _ => throw new Exception("Unhandled case: "+struct)
  }

  /* Like compose, but does not duplicate common terms */
  private def delta_compose(fs1 : FSequent, fs2 :FSequent) = FSequent(
      fs1.antecedent ++ fs2.antecedent.diff(fs1.antecedent),
      fs1.succedent ++ fs2.succedent.diff(fs1.succedent)
    )
}

/**
 * This implements the standard clause set from Bruno's thesis. It has a computational drawback: we create the normalized
 * struct first, which is later on converted to a clause set. The normalized struct easily becomes so big that recursive
 * functions run out of stack. The [[AlternativeStandardClauseSet]] performs a direct conversion, which can handle bigger
 * sizes.
 */
object StandardClauseSet extends Logger {
  override def loggerName = "CeresLogger"

  def normalize(struct:Struct):Struct = struct match {
    case s: A => s
    case s: Dual => s
    case e: EmptyTimesJunction => e
    case e: EmptyPlusJunction => e
    case Plus(s1,s2) => Plus(normalize(s1), normalize(s2))
    case Times(s1,s2,aux) => merge(normalize(s1), normalize(s2),aux)
  }

  def transformStructToClauseSet(struct:Struct) = clausify(normalize(struct))

  def transformStructToLabelledClauseSet(struct:Struct) =
    transformStructToClauseSet(struct).map( so => sequentToLabelledSequent( so ) )


  @tailrec
  def transformCartesianProductToStruct(cp: List[Tuple2[Struct,Struct]],
                                        aux:List[FormulaOccurrence],
                                        acc : List[Struct => Struct]): Struct = cp match {
    case (i,j)::Nil =>
      acc.reverse.foldLeft[Struct](Times(i, j, aux))((struct,fun) => fun(struct))
    case (i,j)::rest =>
      val rec : Struct => Struct = { x => Plus(Times(i,j, aux), x) }
      transformCartesianProductToStruct(rest,aux, rec::acc)

    case Nil =>
      acc.reverse.foldLeft[Struct](EmptyPlusJunction())((struct,fun) => fun(struct))
  }

  private def merge(s1:Struct, s2:Struct, aux: List[FormulaOccurrence]):Struct = {
    info("merge on sizes "+s1.size+" and "+s2.size)
    val (list1,list2) = (getTimesJunctions(s1),getTimesJunctions(s2))
    val cartesianProduct = for (i <- list1; j <- list2) yield (i,j)
    info("done: "+s1.size+" and "+s2.size)
    transformCartesianProductToStruct(cartesianProduct, aux, Nil)
  }


  /** *
    * This is the optimized version of [[slowgetTimesJunctions]] in continuation passing style.
    * @param struct the input struct
    * @return a flattened version of the tree withtimes and junctions
    */
  private def getTimesJunctions(struct:Struct): List[Struct] = getTimesJunctions(struct, (x:List[Struct]) => done(x)).result

  /**
    * This is the optimized version of [[slowgetTimesJunctions]] in continuation passing style.
    * @param struct the input struct
    * @param fun the continuation
    * @return a tailrec object representing the result
    */
  private def getTimesJunctions(struct: Struct, fun : List[Struct] => TailRec[List[Struct]]): TailRec[List[Struct]] = struct match {
    case s: Times => fun(List(s))
    case s: EmptyTimesJunction => fun(List(s))
    case s: A => fun(List(s))
    case s: Dual => fun(List(s))
    case s: EmptyPlusJunction => fun(Nil)
    case Plus(s1,s2) => tailcall(getTimesJunctions(s1, (x:List[Struct]) =>
                                  tailcall(getTimesJunctions(s2, (y:List[Struct]) =>  fun(x:::y)  ))))
  }

  private def slowgetTimesJunctions(struct: Struct):List[Struct] = struct match {
    case s: Times => s::Nil
    case s: EmptyTimesJunction => s::Nil
    case s: A => s::Nil
    case s: Dual => s::Nil
    case s: EmptyPlusJunction => Nil
    case Plus(s1,s2) => slowgetTimesJunctions(s1):::slowgetTimesJunctions(s2)
  }

  private def getLiterals(struct:Struct) : List[Struct] = getLiterals(struct, x => done(x)).result
  private def getLiterals(struct:Struct, fun : List[Struct] => TailRec[List[Struct]] ) : TailRec[List[Struct]] = struct match {
    case s: A => fun(s::Nil)
    case s: Dual => fun(s::Nil)
    case s: EmptyTimesJunction => fun(Nil)
    case s: EmptyPlusJunction => fun(Nil)
    case Plus(s1,s2) => tailcall( getLiterals(s1, x =>
                             tailcall(getLiterals(s2, y => fun(x:::y)) )))
    case Times(s1,s2,_) => tailcall( getLiterals(s1, x =>
                                      tailcall(getLiterals(s2, y => fun(x:::y)) )))
  }

  private def slowgetLiterals(struct:Struct):List[Struct] = struct match {
    case s: A => s::Nil
    case s: Dual => s::Nil
    case s: EmptyTimesJunction => Nil
    case s: EmptyPlusJunction => Nil
    case Plus(s1,s2) => slowgetLiterals(s1):::slowgetLiterals(s2)
    case Times(s1,s2,_) => slowgetLiterals(s1):::slowgetLiterals(s2)
  }


  private def isDual(s:Struct):Boolean = s match {case x: Dual => true; case _ => false}

  private def clausifyTimesJunctions(struct: Struct): Sequent = {
    val literals = getLiterals(struct)
    val (negative,positive) = literals.partition(x => isDual(x))
    val negativeFO: Seq[FormulaOccurrence] = negative.map(x => x.asInstanceOf[Dual].sub.asInstanceOf[A].fo) // extracting the formula occurrences from the negative literal structs
    val positiveFO: Seq[FormulaOccurrence] = positive.map(x => x.asInstanceOf[A].fo)     // extracting the formula occurrences from the positive atomic struct
    Sequent(negativeFO, positiveFO)
  }

  def clausify(struct: Struct): List[Sequent] = {
    val timesJunctions = getTimesJunctions(struct)
    timesJunctions.map(x => clausifyTimesJunctions(x))
  }
}
object SimplifyStruct {
  def apply(s:Struct) : Struct = s match {
    case EmptyPlusJunction() => s
    case EmptyTimesJunction() => s
    case A(_) => s
    case Dual(EmptyPlusJunction()) => EmptyTimesJunction()
    case Dual(EmptyTimesJunction()) => EmptyPlusJunction()
    case Dual(x) => Dual(SimplifyStruct(x))
    case Times(x,EmptyTimesJunction(),_) => SimplifyStruct(x)
    case Times(EmptyTimesJunction(),x,_) => SimplifyStruct(x)
    case Times(x,Dual(y), aux) if x.formula_equal(y) =>
      //println("tautology deleted")
      EmptyPlusJunction()
    case Times(Dual(x),y, aux) if x.formula_equal(y) =>
      //println("tautology deleted")
      EmptyPlusJunction()
    case Times(x,y,aux) =>
      //TODO: adjust aux formulas, they are not needed for the css construction, so we can drop them,
      // but this method should be as general as possible
      Times(SimplifyStruct(x), SimplifyStruct(y), aux)
    case PlusN(terms)  =>
      //println("Checking pluses of "+terms)
      assert(terms.nonEmpty, "Implementation Error: PlusN always unapplies to at least one struct!")
      val nonrendundant_terms = terms.foldLeft[List[Struct]](Nil)((x,term) => {
        val simple = SimplifyStruct(term)
        if (x.filter(_.formula_equal(simple)).nonEmpty )
          x
        else
          simple::x
      })
      /*
      val saved = nonrendundant_terms.size - terms.size
      if (saved >0)
        println("Removed "+ saved + " terms from the struct!")
        */
      PlusN(nonrendundant_terms.reverse)

  }
}


object renameCLsymbols {
  def createMap(cs: List[Sequent]): Map[HOLExpression, HOLExpression] = {
    var i: Int = 1
    var map = Map.empty[HOLExpression, HOLExpression]
    cs.foreach(seq => {
      (seq.antecedent ++ seq.succedent).foreach(fo => {
        fo.formula match {
          case IndexedPredicate(constant, indices) if constant.sym.isInstanceOf[ClauseSetSymbol] => {
            if (!map.contains(constant)) {
              map = map + Tuple2(constant, HOLConst("cl_"+i.toString, Tindex->To) )
              i = i + 1
            }
          }
          case _ => {}
        }
      })
    })
    return map
  }
  
  def apply(cs: List[Sequent]): (List[FSequent], Map[HOLExpression, HOLExpression]) = {
    val map = createMap(cs)
    val list = cs.map(seq => {
      val ant = seq.antecedent.map(fo => {
        fo.formula match {
          case IndexedPredicate(constant, indices) if constant.sym.isInstanceOf[ClauseSetSymbol] => {
            if (map.contains(constant)) {
              HOLApp(map(constant), indices.head)
            }
            else
              throw new Exception("\nError in renameCLsymbols.apply !\n")
          }
          case _ => fo.formula
        }
      })
      val succ = seq.succedent.map(fo => {
        fo.formula match {
          case IndexedPredicate(constant, indices) if constant.sym.isInstanceOf[ClauseSetSymbol] => {
            if (map.contains(constant)) {
              HOLApp(map(constant), indices.head)
            }
            else
              throw new Exception("\nError in renameCLsymbols.apply !\n")
          }
          case _ => fo.formula
        }
      })
      FSequent(ant.asInstanceOf[List[HOLFormula]], succ.asInstanceOf[List[HOLFormula]])
    })
    (list,map)
  }
}
