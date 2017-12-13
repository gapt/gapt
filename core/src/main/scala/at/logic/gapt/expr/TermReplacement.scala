
package at.logic.gapt.expr

import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.ceres._

trait Replaceable[-I, +O] {
  def replace( obj: I, p: PartialFunction[Expr, Expr] ): O

  def names( obj: I ): Set[VarOrConst]
}
trait ClosedUnderReplacement[T] extends Replaceable[T, T]

trait ReplaceableInstances0 {

  implicit object exprReplaceable extends ClosedUnderReplacement[Expr] {
    def replace( term: Expr, map: PartialFunction[Expr, Expr] ): Expr =
      term match {
        case _ if map isDefinedAt term => map( term )

        // special case polymorphic constants so that we can do type-changing replacements
        // but only if the user doesn't specify any replacement for the logical constants
        case Eq( s, t ) if !( map isDefinedAt EqC( s.ty ) ) =>
          Eq( replace( s, map ), replace( t, map ) )
        case All( x, t ) if !( map isDefinedAt ForallC( x.ty ) ) =>
          All( replace( x, map ).asInstanceOf[Var], replace( t, map ) )
        case Ex( x, t ) if !( map isDefinedAt ExistsC( x.ty ) ) =>
          Ex( replace( x, map ).asInstanceOf[Var], replace( t, map ) )

        case App( s, t ) =>
          App( replace( s, map ), replace( t, map ) )
        case Abs( x, t ) =>
          Abs( replace( x, map ).asInstanceOf[Var], replace( t, map ) )

        case _ => term
      }

    def names( term: Expr ): Set[VarOrConst] =
      constants( term ).toSet[VarOrConst] union variables( term ).toSet
  }

  implicit object structReplaceable extends ClosedUnderReplacement[Struct] {
    def replace( st: Struct, map: PartialFunction[Expr, Expr] ): Struct =
      st match {
        case A( x )        => A( TermReplacement( x, map ).asInstanceOf[Formula] )
        case CLS( x, y )   => CLS( TermReplacement( x, map ), y )
        case Dual( x )     => replace( x, map )
        case Times( x, y ) => Times( replace( x, map ), replace( y, map ) )
        case Plus( x, y )  => Plus( replace( x, map ), replace( y, map ) )
        case _             => st
      }
    def names( st: Struct ): Set[VarOrConst] =
      st match {
        case A( x )        => constants( x ).toSet[VarOrConst] union variables( x ).toSet
        case CLS( x, y )   => constants( x ).toSet[VarOrConst] union variables( x ).toSet
        case Dual( x )     => names( x )
        case Times( x, y ) => names( x ) union names( y )
        case Plus( x, y )  => names( x ) union names( y )
        case _             => Set()
      }

  }

}
trait ReplaceableInstances1 extends ReplaceableInstances0 {
  implicit object formulaReplaceable extends ClosedUnderReplacement[Formula] {
    override def replace( obj: Formula, p: PartialFunction[Expr, Expr] ): Formula =
      exprReplaceable.replace( obj, p ).asInstanceOf[Formula]

    def names( obj: Formula ) = exprReplaceable.names( obj )
  }
}

trait ReplaceableInstances2 extends ReplaceableInstances1 {
  implicit def seqReplaceable[I, O]( implicit ev: Replaceable[I, O] ): Replaceable[Seq[I], Seq[O]] =
    new Replaceable[Seq[I], Seq[O]] {
      override def replace( obj: Seq[I], p: PartialFunction[Expr, Expr] ) =
        obj.map { TermReplacement( _, p ) }

      def names( obj: Seq[I] ) = obj flatMap { containedNames( _ ) } toSet
    }
}

object Replaceable extends ReplaceableInstances2 {

  implicit object holAtomReplaceable extends ClosedUnderReplacement[Atom] {
    override def replace( obj: Atom, p: PartialFunction[Expr, Expr] ): Atom =
      exprReplaceable.replace( obj, p ).asInstanceOf[Atom]

    def names( obj: Atom ) = exprReplaceable.names( obj )
  }

  implicit object substitutionReplaceable extends ClosedUnderReplacement[Substitution] {
    def replace( subst: Substitution, p: PartialFunction[Expr, Expr] ): Substitution =
      Substitution( for ( ( l, r ) <- subst.map ) yield TermReplacement( l, p ).asInstanceOf[Var] -> TermReplacement( r, p ) )

    def names( obj: Substitution ) =
      obj.map.keySet ++ obj.map.values flatMap { containedNames( _ ) }
  }

  implicit object definitionReplaceable extends ClosedUnderReplacement[Definition] {
    def replace( definition: Definition, p: PartialFunction[Expr, Expr] ): Definition =
      Definition( TermReplacement( definition.what, p ).asInstanceOf[Const], TermReplacement( definition.by, p ) )

    def names( obj: Definition ) =
      Set[VarOrConst]( obj.what ) union exprReplaceable.names( obj.by )
  }

  implicit def listReplaceable[I, O]( implicit ev: Replaceable[I, O] ): Replaceable[List[I], List[O]] =
    new Replaceable[List[I], List[O]] {
      override def replace( obj: List[I], p: PartialFunction[Expr, Expr] ) =
        obj.map { TermReplacement( _, p ) }

      def names( obj: List[I] ) = obj flatMap { containedNames( _ ) } toSet
    }

  implicit def vectorReplaceable[I, O]( implicit ev: Replaceable[I, O] ): Replaceable[Vector[I], Vector[O]] =
    new Replaceable[Vector[I], Vector[O]] {
      override def replace( obj: Vector[I], p: PartialFunction[Expr, Expr] ) =
        obj.map { TermReplacement( _, p ) }

      def names( obj: Vector[I] ) = obj flatMap { containedNames( _ ) } toSet
    }

  implicit def sequentReplaceable[I, O]( implicit ev: Replaceable[I, O] ): Replaceable[Sequent[I], Sequent[O]] =
    new Replaceable[Sequent[I], Sequent[O]] {
      override def replace( obj: Sequent[I], p: PartialFunction[Expr, Expr] ) =
        obj.map { TermReplacement( _, p ) }

      def names( obj: Sequent[I] ) = obj.elements flatMap { containedNames( _ ) } toSet
    }

  implicit def setReplaceable[I, O]( implicit ev: Replaceable[I, O] ): Replaceable[Set[I], Set[O]] =
    new Replaceable[Set[I], Set[O]] {
      override def replace( obj: Set[I], p: PartialFunction[Expr, Expr] ) =
        obj.map { TermReplacement( _, p ) }

      def names( obj: Set[I] ) = obj flatMap { containedNames( _ ) }
    }

  implicit def optionReplaceable[I, O]( implicit ev: Replaceable[I, O] ): Replaceable[Option[I], Option[O]] =
    new Replaceable[Option[I], Option[O]] {
      override def replace( obj: Option[I], p: PartialFunction[Expr, Expr] ) =
        obj.map { TermReplacement( _, p ) }

      def names( obj: Option[I] ) = obj.toSet[I] flatMap { containedNames( _ ) }
    }

  implicit def tupleReplaceable[I1, I2, O1, O2]( implicit ev1: Replaceable[I1, O1], ev2: Replaceable[I2, O2] ): Replaceable[( I1, I2 ), ( O1, O2 )] =
    new Replaceable[( I1, I2 ), ( O1, O2 )] {
      override def replace( obj: ( I1, I2 ), p: PartialFunction[Expr, Expr] ): ( O1, O2 ) =
        ( ev1.replace( obj._1, p ), ev2.replace( obj._2, p ) )

      def names( obj: ( I1, I2 ) ) = containedNames( obj._1 ) union containedNames( obj._2 )
    }

  implicit def mapReplaceable[I1, I2, O1, O2]( implicit ev1: Replaceable[I1, O1], ev2: Replaceable[I2, O2] ): Replaceable[Map[I1, I2], Map[O1, O2]] =
    new Replaceable[Map[I1, I2], Map[O1, O2]] {
      override def replace( obj: Map[I1, I2], p: PartialFunction[Expr, Expr] ): Map[O1, O2] =
        obj.map( TermReplacement( _, p ) )

      def names( obj: Map[I1, I2] ) = containedNames( obj.toSeq )
    }

  implicit def eitherReplaceable[E, I, O]( implicit ev: Replaceable[I, O] ): Replaceable[Either[E, I], Either[E, O]] =
    new Replaceable[Either[E, I], Either[E, O]] {
      override def replace( obj: Either[E, I], p: PartialFunction[Expr, Expr] ) = obj.map( TermReplacement( _, p ) )
      override def names( obj: Either[E, I] ) = containedNames( obj.toSeq )
    }

  implicit object unitReplaceable extends ClosedUnderReplacement[Unit] {
    override def replace( obj: Unit, p: PartialFunction[Expr, Expr] ): Unit = ()
    override def names( obj: Unit ): Set[VarOrConst] = Set()
  }

}

/**
 * A term replacement homomorphically extends a partial function on lambda expressions to all lambda expressions.
 *
 * This is done on a "best effort" basis.  Replacing constants by ground terms of the same type will usually work, anything beyond that might or might not work.
 */
object TermReplacement {
  def apply( term: Expr, what: Expr, by: Expr ): Expr =
    apply( term, Map( what -> by ) )

  def apply( f: Formula, what: Expr, by: Expr ): Formula =
    apply( f, Map( what -> by ) )

  def apply[I, O]( obj: I, p: PartialFunction[Expr, Expr] )( implicit ev: Replaceable[I, O] ): O =
    ev.replace( obj, p )

  /**
   * Performs capture-avoiding term replacement.
   *
   * If a constant or variable occurs both in the range of partialMap
   * and obj, we rename the occurrence in obj first to something else.
   */
  def hygienic[I, O]( obj: I, partialMap: Map[Const, Expr] )( implicit ev: Replaceable[I, O] ): O = {
    val namesInObj = containedNames( obj )
    val namesInRange = partialMap.values.flatMap { containedNames( _ ) }.toSet

    val needToRename = namesInObj intersect namesInRange -- partialMap.keySet
    val nameGen = rename.awayFrom( namesInObj ++ namesInRange ++ partialMap.keySet )
    val renaming = for ( n <- needToRename ) yield n -> nameGen.fresh( n )

    TermReplacement( obj, partialMap ++ renaming toMap )
  }
}

object containedNames {
  def apply[I, O]( obj: I )( implicit ev: Replaceable[I, O] ): Set[VarOrConst] =
    ev.names( obj )
}

