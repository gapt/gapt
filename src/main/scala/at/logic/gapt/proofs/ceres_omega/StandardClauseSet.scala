/*
 * StandardClauseSet.scala
 *
 */

package at.logic.gapt.proofs.ceres_omega.clauseSets

import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.lkskNew.LKskProof.{ LabelledFormula, LabelledSequent, Label }
import at.logic.gapt.expr._
import at.logic.gapt.utils.logging.Logger
import scala.annotation.tailrec
import scala.util.control.TailCalls._
import at.logic.gapt.proofs.ceres._

/**
 * This implements the clause set transformation of the original CERES method. Specialized extractors exist for
 * CERES_omega and schematic CERES.
 */
object SimpleStandardClauseSet extends SimpleStandardClauseSet

/**
 * Should calculate the same clause set as [[StandardClauseSet]], but without the intermediate representation of a
 * normalized struct. Does not work for Schema, for CERESomega only if all labels are empty (clauses are correct,
 * but labels forgotten).
 */
class SimpleStandardClauseSet {
  def apply( struct: Struct[Label] ): Set[LabelledSequent] = struct match {
    case A( fo, label :: Nil ) =>
      val x: LabelledFormula = ( label, fo )
      Set( Sequent( Nil, List( x ) ) )
    case Dual( A( fo, label :: Nil ) ) =>
      val x: LabelledFormula = ( label, fo )
      Set( Sequent( List( x ), Nil ) )
    case EmptyPlusJunction()            => Set()
    case EmptyTimesJunction()           => Set( Sequent( Nil, Nil ) )
    case Plus( EmptyPlusJunction(), x ) => apply( x )
    case Plus( x, EmptyPlusJunction() ) => apply( x )
    case Plus( A( f1, _ ), Dual( A( f2, _ ) ) ) if f1 == f2 =>
      Set()
    case Plus( Dual( A( f2, _ ) ), A( f1, _ ) ) if f1 == f2 =>
      Set()
    case Plus( x, y ) =>
      apply( x ) ++ apply( y )
    case Times( EmptyTimesJunction(), x, _ ) => apply( x )
    case Times( x, EmptyTimesJunction(), _ ) => apply( x )
    case Times( x, y, _ ) =>
      val xs = apply( x )
      val ys = apply( y )
      xs.flatMap( x1 => ys.flatMap( y1 => Set( delta_compose( x1, y1 ) ) ) )
    case _ => throw new Exception( "Unhandled case: " + struct )
  }

  /* Like compose, but does not duplicate common terms */
  private def delta_compose( fs1: LabelledSequent, fs2: LabelledSequent ) = Sequent(
    fs1.antecedent ++ fs2.antecedent.diff( fs1.antecedent ),
    fs1.succedent ++ fs2.succedent.diff( fs1.succedent )
  )
}

/**
 * This implements the standard clause set from Bruno's thesis. It has a computational drawback: we create the normalized
 * struct first, which is later on converted to a clause set. The normalized struct easily becomes so big that recursive
 * functions run out of stack. The [[SimpleStandardClauseSet]] performs a direct conversion, which can handle bigger
 * sizes.
 */
object StandardClauseSet extends Logger {
  override def loggerName = "CeresLogger"

  def normalize( struct: Struct[Label] ): Struct[Label] = struct match {
    case s: A[Label]          => s
    case s: Dual[Label]       => s
    case EmptyTimesJunction() => struct
    case EmptyPlusJunction()  => struct
    case Plus( s1, s2 )       => Plus( normalize( s1 ), normalize( s2 ) )
    case Times( s1, s2, aux ) => merge( normalize( s1 ), normalize( s2 ) )
  }

  def transformStructToClauseSet( struct: Struct[Label] ): List[LabelledSequent] = clausify( normalize( struct ) )

  @tailrec
  def transformCartesianProductToStruct[Data](
    cp:  List[Tuple2[Struct[Data], Struct[Data]]],
    acc: List[Struct[Data] => Struct[Data]]
  ): Struct[Data] = cp match {
    case ( i, j ) :: Nil =>
      acc.reverse.foldLeft[Struct[Data]]( Times( i, j, Nil ) )( ( struct, fun ) => fun( struct ) )
    case ( i, j ) :: rest =>
      val rec: Struct[Data] => Struct[Data] = { x => Plus( Times( i, j, Nil ), x ) }
      transformCartesianProductToStruct( rest, rec :: acc )

    case Nil =>
      acc.reverse.foldLeft[Struct[Data]]( EmptyPlusJunction() )( ( struct, fun ) => fun( struct ) )
  }

  private def merge[Data]( s1: Struct[Data], s2: Struct[Data] ): Struct[Data] = {
    trace( "merge on sizes " + s1.size + " and " + s2.size )
    val ( list1, list2 ) = ( getTimesJunctions( s1 ), getTimesJunctions( s2 ) )
    val cartesianProduct = for ( i <- list1; j <- list2 ) yield ( i, j )
    trace( "done: " + s1.size + " and " + s2.size )
    transformCartesianProductToStruct( cartesianProduct, Nil )
  }

  /**
   * *
   * This is the optimized version of [[slowgetTimesJunctions]] in continuation passing style.
   * @param struct the input struct
   * @return a flattened version of the tree withtimes and junctions
   */
  private def getTimesJunctions[Data]( struct: Struct[Data] ): List[Struct[Data]] =
    getTimesJunctions( struct, ( x: List[Struct[Data]] ) => done( x ) ).result

  /**
   * This is the optimized version of [[slowgetTimesJunctions]] in continuation passing style.
   * @param struct the input struct
   * @param fun the continuation
   * @return a tailrec object representing the result
   */
  private def getTimesJunctions[Data]( struct: Struct[Data], fun: List[Struct[Data]] => TailRec[List[Struct[Data]]] ): TailRec[List[Struct[Data]]] = struct match {
    case Times( _, _, _ )     => fun( List( struct ) )
    case EmptyTimesJunction() => fun( List( struct ) )
    case A( _, _ )            => fun( List( struct ) )
    case Dual( _ )            => fun( List( struct ) )
    case EmptyPlusJunction()  => fun( Nil )
    case Plus( s1, s2 ) => tailcall( getTimesJunctions( s1, ( x: List[Struct[Data]] ) =>
      tailcall( getTimesJunctions( s2, ( y: List[Struct[Data]] ) => fun( x ::: y ) ) ) ) )
  }

  private def slowgetTimesJunctions[Data]( struct: Struct[Data] ): List[Struct[Data]] = struct match {
    case Times( _, _, _ )     => struct :: Nil
    case EmptyTimesJunction() => struct :: Nil
    case A( _, _ )            => struct :: Nil
    case Dual( _ )            => struct :: Nil
    case EmptyPlusJunction()  => Nil
    case Plus( s1, s2 )       => slowgetTimesJunctions( s1 ) ::: slowgetTimesJunctions( s2 )
  }

  private def getLiterals[Data]( struct: Struct[Data] ): List[Struct[Data]] = getLiterals( struct, ( x: List[Struct[Data]] ) => done( x ) ).result
  private def getLiterals[Data]( struct: Struct[Data], fun: List[Struct[Data]] => TailRec[List[Struct[Data]]] ): TailRec[List[Struct[Data]]] = struct match {
    case s: A[Data]           => fun( s :: Nil )
    case s: Dual[Data]        => fun( s :: Nil )
    case EmptyTimesJunction() => fun( Nil )
    case EmptyPlusJunction()  => fun( Nil )
    case Plus( s1, s2 ) => tailcall( getLiterals( s1, ( x: List[Struct[Data]] ) =>
      tailcall( getLiterals( s2, ( y: List[Struct[Data]] ) => fun( x ::: y ) ) ) ) )
    case Times( s1, s2, _ ) => tailcall( getLiterals[Data]( s1, ( x: List[Struct[Data]] ) =>
      tailcall( getLiterals( s2, ( y: List[Struct[Data]] ) => fun( x ::: y ) ) ) ) )
  }

  private def slowgetLiterals[Data]( struct: Struct[Data] ): List[Struct[Data]] = struct match {
    case s: A[Data]           => s :: Nil
    case s: Dual[Data]        => s :: Nil
    case EmptyTimesJunction() => Nil
    case EmptyPlusJunction()  => Nil
    case Plus( s1, s2 )       => slowgetLiterals( s1 ) ::: slowgetLiterals( s2 )
    case Times( s1, s2, _ )   => slowgetLiterals( s1 ) ::: slowgetLiterals( s2 )
  }

  private def clausifyTimesJunctions( struct: Struct[Label] ): LabelledSequent = {
    val literals = getLiterals( struct )
    val ( negative, positive ) =
      literals.foldLeft( List[LabelledFormula](), List[LabelledFormula]() )( ( pair, s ) => {
        val ( ns, ps ) = pair
        s match {
          case Dual( A( f, label :: Nil ) ) => ( ( label, f ) :: ns, ps )
          case A( f, label :: Nil )         => ( ns, ( label, f ) :: ps )
        }
      } )

    Sequent( negative, positive )
  }

  def clausify( struct: Struct[Label] ): List[LabelledSequent] = {
    val timesJunctions = getTimesJunctions( struct )
    timesJunctions.map( x => clausifyTimesJunctions( x ) )
  }
}
