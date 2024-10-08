package gapt.expr

import gapt.expr.formula.All
import gapt.expr.formula.Atom
import gapt.expr.formula.Eq
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.constants.EqC
import gapt.expr.formula.constants.ExistsC
import gapt.expr.formula.constants.ForallC
import gapt.expr.subst.Substitution
import gapt.expr.ty.{TArr, TBase, TVar, Ty}
import gapt.expr.util.constants
import gapt.expr.util.rename
import gapt.expr.util.variables
import gapt.proofs.Sequent
import gapt.proofs.ceres._
import gapt.proofs.context.update.Definition

trait Replaceable[-I, +O] {
  def replace(obj: I, p: PartialFunction[Expr, Expr]): O

  def names(obj: I): Set[VarOrConst]
}
trait ReplaceableInstances0 {

  implicit object exprReplaceable extends ClosedUnderReplacement[Expr] {
    def replace(term: Expr, map: PartialFunction[Expr, Expr]): Expr =
      term match {
        case _ if map isDefinedAt term => map(term)

        // special case polymorphic constants so that we can do type-changing replacements
        // but only if the user doesn't specify any replacement for the logical constants
        case Eq(s, t) if !(map isDefinedAt EqC(s.ty)) =>
          Eq(replace(s, map), replace(t, map))
        case All(x, t) if !(map isDefinedAt ForallC(x.ty)) =>
          All(replace(x, map).asInstanceOf[Var], replace(t, map))
        case Ex(x, t) if !(map isDefinedAt ExistsC(x.ty)) =>
          Ex(replace(x, map).asInstanceOf[Var], replace(t, map))

        case App(s, t) =>
          App(replace(s, map), replace(t, map))
        case Abs(x, t) =>
          Abs(replace(x, map).asInstanceOf[Var], replace(t, map))

        case _ => term
      }

    def names(term: Expr): Set[VarOrConst] =
      constants.nonLogical(term).toSet[VarOrConst] union variables(term).toSet
  }

  implicit object structReplaceable extends ClosedUnderReplacement[Struct] {
    def replace(st: Struct, map: PartialFunction[Expr, Expr]): Struct =
      st match {
        case A(x)        => A(TermReplacement(x, map).asInstanceOf[Formula])
        case CLS(x, y)   => CLS(TermReplacement(x, map), y)
        case Dual(x)     => replace(x, map)
        case Times(x, y) => Times(replace(x, map), replace(y, map))
        case Plus(x, y)  => Plus(replace(x, map), replace(y, map))
        case _           => st
      }
    def names(st: Struct): Set[VarOrConst] =
      st match {
        case A(x)        => constants.nonLogical(x).toSet[VarOrConst] union variables(x).toSet
        case CLS(x, y)   => constants.nonLogical(x).toSet[VarOrConst] union variables(x).toSet
        case Dual(x)     => names(x)
        case Times(x, y) => names(x) union names(y)
        case Plus(x, y)  => names(x) union names(y)
        case _           => Set()
      }

  }

}
trait ReplaceableInstances1 extends ReplaceableInstances0 {
  implicit object formulaReplaceable extends ClosedUnderReplacement[Formula] {
    override def replace(obj: Formula, p: PartialFunction[Expr, Expr]): Formula =
      exprReplaceable.replace(obj, p).asInstanceOf[Formula]

    def names(obj: Formula): Set[VarOrConst] = exprReplaceable.names(obj)
  }
}

trait ReplaceableInstances2 extends ReplaceableInstances1 {
  implicit def seqReplaceable[I, O](implicit ev: Replaceable[I, O]): Replaceable[Seq[I], Seq[O]] =
    new Replaceable[Seq[I], Seq[O]] {
      override def replace(obj: Seq[I], p: PartialFunction[Expr, Expr]): Seq[O] =
        obj.map { TermReplacement(_, p) }

      def names(obj: Seq[I]): Set[VarOrConst] = obj flatMap { containedNames(_) } toSet
    }
}

object Replaceable extends ReplaceableInstances2 {

  implicit object holAtomReplaceable extends ClosedUnderReplacement[Atom] {
    override def replace(obj: Atom, p: PartialFunction[Expr, Expr]): Atom =
      exprReplaceable.replace(obj, p).asInstanceOf[Atom]

    def names(obj: Atom): Set[VarOrConst] = exprReplaceable.names(obj)
  }

  implicit object substitutionReplaceable extends ClosedUnderReplacement[Substitution] {
    def replace(subst: Substitution, p: PartialFunction[Expr, Expr]): Substitution =
      Substitution(for ((l, r) <- subst.map) yield TermReplacement(l, p).asInstanceOf[Var] -> TermReplacement(r, p))

    def names(obj: Substitution): Set[VarOrConst] =
      obj.map.keySet ++ obj.map.values flatMap { containedNames(_) }
  }

  implicit object definitionReplaceable extends ClosedUnderReplacement[Definition] {
    def replace(definition: Definition, p: PartialFunction[Expr, Expr]): Definition =
      Definition(TermReplacement(definition.what, p).asInstanceOf[Const], TermReplacement(definition.by, p))

    def names(obj: Definition): Set[VarOrConst] =
      Set[VarOrConst](obj.what) union exprReplaceable.names(obj.by)
  }

  implicit def listReplaceable[I, O](implicit ev: Replaceable[I, O]): Replaceable[List[I], List[O]] =
    new Replaceable[List[I], List[O]] {
      override def replace(obj: List[I], p: PartialFunction[Expr, Expr]): List[O] =
        obj.map { TermReplacement(_, p) }

      def names(obj: List[I]): Set[VarOrConst] = obj flatMap { containedNames(_) } toSet
    }

  implicit def vectorReplaceable[I, O](implicit ev: Replaceable[I, O]): Replaceable[Vector[I], Vector[O]] =
    new Replaceable[Vector[I], Vector[O]] {
      override def replace(obj: Vector[I], p: PartialFunction[Expr, Expr]): Vector[O] =
        obj.map { TermReplacement(_, p) }

      def names(obj: Vector[I]): Set[VarOrConst] = obj flatMap { containedNames(_) } toSet
    }

  implicit def sequentReplaceable[I, O](implicit ev: Replaceable[I, O]): Replaceable[Sequent[I], Sequent[O]] =
    new Replaceable[Sequent[I], Sequent[O]] {
      override def replace(obj: Sequent[I], p: PartialFunction[Expr, Expr]): Sequent[O] =
        obj.map { TermReplacement(_, p) }

      def names(obj: Sequent[I]): Set[VarOrConst] = obj.elements flatMap { containedNames(_) } toSet
    }

  implicit def setReplaceable[I, O](implicit ev: Replaceable[I, O]): Replaceable[Set[I], Set[O]] =
    new Replaceable[Set[I], Set[O]] {
      override def replace(obj: Set[I], p: PartialFunction[Expr, Expr]): Set[O] =
        obj.map { TermReplacement(_, p) }

      def names(obj: Set[I]): Set[VarOrConst] = obj flatMap { containedNames(_) }
    }

  implicit def optionReplaceable[I, O](implicit ev: Replaceable[I, O]): Replaceable[Option[I], Option[O]] =
    new Replaceable[Option[I], Option[O]] {
      override def replace(obj: Option[I], p: PartialFunction[Expr, Expr]): Option[O] =
        obj.map { TermReplacement(_, p) }

      def names(obj: Option[I]): Set[VarOrConst] = obj.toSet[I] flatMap { containedNames(_) }
    }

  implicit def tupleReplaceable[I1, I2, O1, O2](implicit ev1: Replaceable[I1, O1], ev2: Replaceable[I2, O2]): Replaceable[(I1, I2), (O1, O2)] =
    new Replaceable[(I1, I2), (O1, O2)] {
      override def replace(obj: (I1, I2), p: PartialFunction[Expr, Expr]): (O1, O2) =
        (ev1.replace(obj._1, p), ev2.replace(obj._2, p))

      def names(obj: (I1, I2)): Set[VarOrConst] = containedNames(obj._1) union containedNames(obj._2)
    }

  implicit def mapReplaceable[I1, I2, O1, O2](implicit ev1: Replaceable[I1, O1], ev2: Replaceable[I2, O2]): Replaceable[Map[I1, I2], Map[O1, O2]] =
    new Replaceable[Map[I1, I2], Map[O1, O2]] {
      override def replace(obj: Map[I1, I2], p: PartialFunction[Expr, Expr]): Map[O1, O2] =
        obj.map(TermReplacement(_, p))

      def names(obj: Map[I1, I2]) = containedNames(obj.toSeq)
    }

  implicit def eitherReplaceable[E, I, O](implicit ev: Replaceable[I, O]): Replaceable[Either[E, I], Either[E, O]] =
    new Replaceable[Either[E, I], Either[E, O]] {
      override def replace(obj: Either[E, I], p: PartialFunction[Expr, Expr]): Either[E, O] = obj.map(TermReplacement(_, p))
      override def names(obj: Either[E, I]) = containedNames(obj.toSeq)
    }

  implicit object unitReplaceable extends ClosedUnderReplacement[Unit] {
    override def replace(obj: Unit, p: PartialFunction[Expr, Expr]): Unit = ()
    override def names(obj: Unit): Set[VarOrConst] = Set()
  }

}

/**
 * A term replacement homomorphically extends a partial function on lambda expressions to all lambda expressions.
 *
 * This is done on a "best effort" basis.  Replacing constants by ground terms of the same type will usually work, anything beyond that might or might not work.
 */
object TermReplacement {
  def apply(term: Expr, what: Expr, by: Expr): Expr =
    apply(term, Map(what -> by))

  def apply(f: Formula, what: Expr, by: Expr): Formula =
    apply(f, Map(what -> by))

  def apply[I, O](obj: I, p: PartialFunction[Expr, Expr])(implicit ev: Replaceable[I, O]): O =
    ev.replace(obj, p)

  /**
   * Performs capture-avoiding term replacement.
   *
   * If a constant or variable occurs both in the range of partialMap
   * and obj, we rename the occurrence in obj first to something else.
   */
  def hygienic[I, O](obj: I, partialMap: Map[Const, Expr])(implicit ev: Replaceable[I, O]): O = {
    val namesInObj = containedNames(obj)
    val namesInRange = partialMap.values.flatMap { containedNames(_) }.toSet

    val needToRename = namesInObj intersect namesInRange -- partialMap.keySet
    val nameGen = rename.awayFrom(namesInObj ++ namesInRange ++ partialMap.keySet)
    val renaming = for (n <- needToRename) yield n -> nameGen.fresh(n)

    TermReplacement(obj, partialMap ++ renaming toMap)
  }

  def apply[T: ClosedUnderReplacement](t: T, replacements: Map[Const, Expr], tyReplacements: Map[TBase, Ty]): T = {
    def replTyInN(n: VarOrConst): VarOrConst =
      n match {
        case Const(n, t, ps) => Const(n, replTy(t), ps map replTy)
        case Var(n, t)       => Var(n, replTy(t))
      }
    def replTy(t: Ty): Ty =
      t match {
        case t: TVar => t
        case t @ TBase(n, ps) =>
          tyReplacements.getOrElse(t, TBase(n, ps map replTy))
        case TArr(t1, t2) =>
          replTy(t1) ->: replTy(t2)
      }

    val namesInObj = containedNames(t)
    val namesInRange = replacements.values.flatMap { containedNames(_) }.toSet // TODO: types

    val nameGen = rename.awayFrom(namesInObj ++ namesInRange ++ replacements.keySet)
    val renaming = for (n <- namesInObj if !replacements.toMap[VarOrConst, Expr].contains(n)) yield n -> replTyInN(if (namesInRange.contains(replTyInN(n))) nameGen.fresh(n) else n)

    TermReplacement(t, replacements.asInstanceOf[Map[Expr, Expr]] ++ renaming)
  }

  def undoGrounding[T: ClosedUnderReplacement](t: T, subst: Substitution): T =
    apply(
      t,
      subst.map.collect { case (v, c: Const) => c -> v },
      subst.typeMap.collect { case (v, c: TBase) => c -> v }
    )

}

object containedNames {
  def apply[I, O](obj: I)(implicit ev: Replaceable[I, O]): Set[VarOrConst] =
    ev.names(obj)
}
