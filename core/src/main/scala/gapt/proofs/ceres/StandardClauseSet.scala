/*
 * StandardClauseSet.scala
 *
 */

package gapt.proofs.ceres

import gapt.proofs.{HOLClause, Sequent, SetSequent}
import gapt.expr._
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Top

/**
 * Calculates the characteristic clause set
 */
class CharacteristicClauseSet {
  def apply(struct: Struct): Set[SetSequent[Atom]] = struct match {
    case A(fo: Atom) => Set(SetSequent[Atom](Sequent(Nil, List(fo))))
    case A(Top())    => Set()
    case A(Bottom()) => Set(SetSequent[Atom](Sequent(Nil, Nil)))
    case A(f) =>
      throw new Exception(s"Encountered a formula $f as leaf in the struct. Can't convert it to a clause.")
    case Dual(A(fo: Atom)) => Set(SetSequent[Atom](Sequent(List(fo), Nil)))
    case Dual(A(Top()))    => Set(SetSequent[Atom](Sequent(Nil, Nil)))
    case Dual(A(Bottom())) => Set()
    case Dual(A(f)) =>
      throw new Exception(s"Encountered a formula $f as leaf in the struct. Can't convert it to a clause.")
    case EmptyPlusJunction()            => Set()
    case EmptyTimesJunction()           => Set(SetSequent[Atom](Sequent(Nil, Nil)))
    case Plus(EmptyPlusJunction(), x)   => apply(x)
    case Plus(x, EmptyPlusJunction())   => apply(x)
    case Plus(x, y)                     => apply(x) ++ apply(y)
    case Times(EmptyTimesJunction(), x) => apply(x)
    case Times(x, EmptyTimesJunction()) => apply(x)
    case Times(A(f1), Dual(A(f2))) if f1 == f2 => // would result in a tautology f :- f
      Set()
    case Times(Dual(A(f2)), A(f1)) if f1 == f2 => // would result in a tautology f :- f
      Set()
    case Times(x, y) =>
      val xs = apply(x)
      val ys = apply(y)
      xs.flatMap((x1: SetSequent[Atom]) =>
        ys.flatMap((y1: SetSequent[Atom]) => {
          delta_compose(x1, y1) match {
            case Some(m) => Set(m)
            case None    => Set()
          }
        })
      )
    case _ => throw new Exception("Unhandled case: " + struct)
  }

  private def compose[T](fs1: Sequent[T], fs2: Sequent[T]) = fs1 ++ fs2

  /* Like compose, but does not duplicate common terms */
  private def delta_compose[T](fs1: SetSequent[T], fs2: SetSequent[T]): Option[SetSequent[T]] = {
    val ante1 = fs1.sequent.antecedent.distinct.toSet ++ fs2.sequent.antecedent.distinct.toSet.diff(fs1.sequent.antecedent.distinct.toSet)
    val suc1 = fs1.sequent.succedent.distinct.toSet ++ fs2.sequent.succedent.distinct.toSet.diff(fs1.sequent.succedent.distinct.toSet)
    val anteSucInter = ante1 & suc1
    if (anteSucInter.isEmpty) Some(SetSequent[T](Sequent[T](ante1.toSeq, suc1.toSeq)))
    else None

  }
}

object CharacteristicClauseSet {

  def apply(struct: Struct): Set[HOLClause] = (new CharacteristicClauseSet)(struct).map(y => y.sequent)
}

object SimplifyStruct {
  def apply(s: Struct): Struct = s match {
    case EmptyPlusJunction()                     => s
    case EmptyTimesJunction()                    => s
    case A(_)                                    => s
    case Dual(EmptyPlusJunction())               => EmptyTimesJunction()
    case Dual(EmptyTimesJunction())              => EmptyPlusJunction()
    case Dual(x)                                 => Dual(SimplifyStruct(x))
    case Times(x, EmptyTimesJunction())          => SimplifyStruct(x)
    case Times(EmptyTimesJunction(), x)          => SimplifyStruct(x)
    case Times(x, Dual(y)) if x.formula_equal(y) =>
      // println("tautology deleted")
      EmptyPlusJunction()
    case Times(Dual(x), y) if x.formula_equal(y) =>
      // println("tautology deleted")
      EmptyPlusJunction()
    case Times(x, y) =>
      // TODO: adjust aux formulas, they are not needed for the css construction, so we can drop them,
      // but this method should be as general as possible
      Times(SimplifyStruct(x), SimplifyStruct(y))
    case PlusN(terms) =>
      // println("Checking pluses of "+terms)
      assert(terms.nonEmpty, "Implementation Error: PlusN always unapplies to at least one struct!")
      val nonrendundant_terms = terms.foldLeft[List[Struct]](Nil)((x, term) => {
        val simple = SimplifyStruct(term)
        if (x.filter(_.formula_equal(simple)).nonEmpty)
          x
        else
          simple :: x
      })
      PlusN(nonrendundant_terms.reverse)

  }
}
