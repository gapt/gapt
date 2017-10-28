/*
 * StandardClauseSet.scala
 *
 */

package at.logic.gapt.proofs.ceres

import at.logic.gapt.proofs.{HOLClause, HOLSequent, Sequent}
import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.{CLSTerm, SequentComposition}

/**
 * Calculates the characteristic clause set
 */
class CharacteristicClauseSet[Data] {
  def apply(
    struct:           Struct[Data],
    cutConfiguration: HOLSequent = HOLSequent(List(), List()) ): Set[SequentComposition] =  struct match {
      case A(fo: Atom, _) =>
        Set(SequentComposition(Sequent(Nil, List(fo))))
      case A(Top(), _) =>
        Set()
      case A(Bottom(), _) =>
        Set(SequentComposition(Sequent(Nil, Nil)))
      case A(f, _) =>
        throw new Exception(s"Encountered a formula $f as leaf in the struct. Can't convert it to a clause.")
      case Dual(A(fo: Atom, _)) =>
        Set(SequentComposition(Sequent(List(fo), Nil)))
      case Dual(A(Top(), _)) =>
        Set(SequentComposition(Sequent(Nil, Nil)))
      case Dual(A(Bottom(), _)) =>
        Set()
      case Dual(A(f, _)) =>
        throw new Exception(s"Encountered a formula $f as leaf in the struct. Can't convert it to a clause.")
      case EmptyPlusJunction() =>
        Set()
      case EmptyTimesJunction() =>
        Set(SequentComposition(Sequent(Nil, Nil)))
      case Plus(EmptyPlusJunction(), x) =>
        apply(x, cutConfiguration)
      case Plus(x, EmptyPlusJunction()) =>
        apply(x, cutConfiguration)
      case Plus(x, y) =>
        apply(x, cutConfiguration) ++ apply(y, cutConfiguration)

      case Times(EmptyTimesJunction(), x, _) =>
        apply(x, cutConfiguration)
      case Times(x, EmptyTimesJunction(), _) =>
        apply(x, cutConfiguration)

      case Times(A(f1, _), Dual(A(f2, _)), _) if f1 == f2 => //would result in a tautology f :- f
        Set()
      case Times(Dual(A(f2, _)), A(f1, _), _) if f1 == f2 => //would result in a tautology f :- f
        Set()
      case Times(x, y, _) =>
        val xs = apply(x, cutConfiguration)
        val ys = apply(y, cutConfiguration)
        xs.flatMap((x1: SequentComposition) => ys.flatMap((y1: SequentComposition) => {

          delta_compose(x1, y1) match {
            case Some(m) => Set(m).toTraversable
            case None => Set().toTraversable
          }
        }))
      case CLS(proof, cconfig, fv, _) =>
        Set(SequentComposition(CLSTerm(proof, cconfig, fv)))
      case _ =>
        throw new Exception("Unhandled case: " + struct)
    }

  /* Like compose, but does not duplicate common terms */
  private def delta_compose[T]( fs1: SequentComposition, fs2: SequentComposition ): Option[SequentComposition] = {
    if(fs1.isUniformTorwards[T]() && fs2.isUniformTorwards[T]()) {
      val leftSide = fs1.towards[T]()
      val rightSide = fs2.towards[T]()
      val ante1 = leftSide.antecedent.distinct.toSet ++ rightSide.antecedent.distinct.toSet.diff(leftSide.antecedent.distinct.toSet)
      val suc1 = leftSide.succedent.distinct.toSet ++ rightSide.succedent.distinct.toSet.diff(leftSide.succedent.distinct.toSet)
      val anteSucInter = ante1 & suc1
      if (anteSucInter.isEmpty) Some(SequentComposition(Sequent[T](ante1.toSeq, suc1.toSeq)))
      else None
    }
    else if(fs1.isUniformTorwards[T]() &&  fs2.isCompositeawayFrom[T]()) {
      val leftSide = fs1.towards[T]()
      val rightSideGood = fs2.towards[T]()
      val rightSideBad = fs2.awayFrom[T]()
      val ante1 = leftSide.antecedent.distinct.toSet ++ rightSideGood.antecedent.distinct.toSet.diff(leftSide.antecedent.distinct.toSet)
      val suc1 = leftSide.succedent.distinct.toSet ++ rightSideGood.succedent.distinct.toSet.diff(leftSide.succedent.distinct.toSet)
      val anteSucInter = ante1 & suc1
      if (anteSucInter.isEmpty)
        Some(SequentComposition(rightSideBad.composedSequents +Sequent[T](ante1.toSeq, suc1.toSeq)))
      else Some(rightSideBad)
    }
    else if(fs2.isUniformTorwards[T]() &&  fs1.isCompositeawayFrom[T]()) {
      val leftSidegood = fs1.towards[T]()
      val leftSideBad = fs2.awayFrom[T]()
      val rightSide = fs2.towards[T]()
      val ante1 = leftSidegood.antecedent.distinct.toSet ++ rightSide.antecedent.distinct.toSet.diff(leftSidegood.antecedent.distinct.toSet)
      val suc1 = leftSidegood.succedent.distinct.toSet ++ rightSide.succedent.distinct.toSet.diff(leftSidegood.succedent.distinct.toSet)
      val anteSucInter = ante1 & suc1
      if (anteSucInter.isEmpty)
        Some(SequentComposition(leftSideBad.composedSequents + Sequent[T](ante1.toSeq, suc1.toSeq)))
      else Some(leftSideBad)
    }
    else {
      val leftSidegood = fs1.towards[T]()
      val leftSideBad = fs2.awayFrom[T]()
      val rightSideGood = fs2.towards[T]()
      val rightSideBad = fs2.awayFrom[T]()
      val ante1 = leftSidegood.antecedent.distinct.toSet ++ rightSideGood.antecedent.distinct.toSet.diff(leftSidegood.antecedent.distinct.toSet)
      val suc1 = leftSidegood.succedent.distinct.toSet ++ rightSideGood.succedent.distinct.toSet.diff(leftSidegood.succedent.distinct.toSet)
      val anteSucInter = ante1 & suc1
      if (anteSucInter.isEmpty)
        Some(SequentComposition(leftSideBad.composedSequents++rightSideBad.composedSequents + Sequent[T](ante1.toSeq, suc1.toSeq)))
      else Some(SequentComposition(leftSideBad.composedSequents++rightSideBad.composedSequents))
    }

  }
}

object CharacteristicClauseSet {
  def apply[Data](struct: Struct[Data]): Option[Set[HOLClause]] = {
    val result = (new CharacteristicClauseSet[Data]) (struct)
    if (result.forall(y => y.isUniformTorwards[Atom]()))
      Some(result.map(y => y.towards[Atom]()))
    else None
  }

  def apply[Data](struct: Struct[Data], cutConfiguration: HOLSequent): Set[SequentComposition] =
    (new CharacteristicClauseSet[Data]) (struct, cutConfiguration)
}

  object SimplifyStruct {
    def apply[Data](s: Struct[Data]): Struct[Data] = s match {
      case EmptyPlusJunction() => s
      case EmptyTimesJunction() => s
      case A(_, _) => s
      case Dual(EmptyPlusJunction()) => EmptyTimesJunction()
      case Dual(EmptyTimesJunction()) => EmptyPlusJunction()
      case Dual(x) => Dual(SimplifyStruct(x))
      case Times(x, EmptyTimesJunction(), _) => SimplifyStruct(x)
      case Times(EmptyTimesJunction(), x, _) => SimplifyStruct(x)
      case Times(x, Dual(y), aux) if x.formula_equal(y) =>
        //println("tautology deleted")
        EmptyPlusJunction()
      case Times(Dual(x), y, aux) if x.formula_equal(y) =>
        //println("tautology deleted")
        EmptyPlusJunction()
      case Times(x, y, aux) =>
        //TODO: adjust aux formulas, they are not needed for the css construction, so we can drop them,
        // but this method should be as general as possible
        Times(SimplifyStruct(x), SimplifyStruct(y), aux)
      case PlusN(terms) =>
        //println("Checking pluses of "+terms)
        assert(terms.nonEmpty, "Implementation Error: PlusN always unapplies to at least one struct!")
        val nonrendundant_terms = terms.foldLeft[List[Struct[Data]]](Nil)((x, term) => {
          val simple = SimplifyStruct(term)
          if (x.filter(_.formula_equal(simple)).nonEmpty)
            x
          else
            simple :: x
        })
        PlusN(nonrendundant_terms.reverse)
    }
  }


