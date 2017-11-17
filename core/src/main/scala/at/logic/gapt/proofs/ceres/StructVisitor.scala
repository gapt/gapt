package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr.{ Atom, Expr, Formula }
import at.logic.gapt.proofs.Sequent

trait StructVisitor[Ret, T] {
  final def recurse[Data](
    struct:    Struct[Data],
    tranform:  StructTransformer[Ret, T],
    otherArgs: T ): Ret = struct match {
    case A( a: Atom, _ )      => visitAtomLeaf( a, tranform, otherArgs )
    case EmptyPlusJunction()  => visitEmptyPlusJunction( tranform, otherArgs )
    case EmptyTimesJunction() => visitEmptyTimesJunction( tranform, otherArgs )
    case Dual( x )            => visitDual( x, tranform, otherArgs )
    case Plus( x, y )         => visitPlus( x, y, tranform, otherArgs )
    case Times( x, y, _ )     => visitTimes( x, y, tranform, otherArgs )
    case CLS( x, y )          => visitCLS( x, y, tranform, otherArgs )
    case _                    => throw new Exception( "Unhandled case: " + struct )
  }
  def visitDual[Data](
    struct:    Struct[Data],
    tranform:  StructTransformer[Ret, T],
    otherArgs: T ): Ret = {
    val tranform2 = StructTransformer[Ret, T]( tranform.aF, tranform.tF, tranform.tD, tranform.pF, tranform.pD, tranform.dF, tranform.cF )
    tranform.dF( recurse( struct, tranform2, otherArgs ), otherArgs )
  }
  def visitAtomLeaf[Data](
    f:         Formula,
    tranform:  StructTransformer[Ret, T],
    otherArgs: T ): Ret = {
    tranform.aF( f, otherArgs )
  }
  def visitEmptyPlusJunction( tranform: StructTransformer[Ret, T], otherArgs: T ): Ret = tranform.pD
  def visitEmptyTimesJunction( tranform: StructTransformer[Ret, T], otherArgs: T ): Ret = tranform.tD
  def visitPlus[Data](
    struct1:   Struct[Data],
    struct2:   Struct[Data],
    tranform:  StructTransformer[Ret, T],
    otherArgs: T ): Ret = tranform.pF(
    recurse( struct1, tranform, otherArgs ),
    recurse( struct2, tranform, otherArgs ),
    otherArgs )
  def visitTimes[Data](
    struct1:   Struct[Data],
    struct2:   Struct[Data],
    tranform:  StructTransformer[Ret, T],
    otherArgs: T ): Ret = tranform.tF(
    recurse( struct1, tranform, otherArgs ),
    recurse( struct2, tranform, otherArgs ), otherArgs )
  def visitCLS[Data]( ex: Expr, sb: Sequent[Boolean],
                      tranform:  StructTransformer[Ret, T],
                      otherArgs: T ): Ret = tranform.cF( ex, sb, otherArgs )

}
case class StructTransformer[Ret, T](
    aF: ( Formula, T ) => Ret,
    pF: ( Ret, Ret, T ) => Ret,
    pD: Ret,
    tF: ( Ret, Ret, T ) => Ret,
    tD: Ret, dF: ( Ret, T ) => Ret,
    cF: ( Expr, Sequent[Boolean], T ) => Ret ) {}
