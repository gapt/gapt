package at.logic.gapt.proofs.congruence

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ HOLClause, Sequent, SequentProof }

trait CongruenceProof extends SequentProof[Atom, CongruenceProof] {
  def lhs: Expr
  def rhs: Expr
  def equation = Eq( lhs, rhs )

  override def conclusion: HOLClause = Sequent() :+ equation

  override def occConnectors = throw new NotImplementedError
  override def mainIndices = throw new NotImplementedError
  override def auxIndices = throw new NotImplementedError

  def *( that: CongruenceProof ): CongruenceProof = Trans.ifNecessary( this, that )
  def inv: CongruenceProof = Symm.ifNecessary( this )
}

case class Input( eq: Formula ) extends CongruenceProof {
  val Eq( lhs, rhs ) = eq

  override def immediateSubProofs = Seq()
}

case class Refl( e: Expr ) extends CongruenceProof {
  val ( lhs, rhs ) = ( e, e )

  override def immediateSubProofs = Seq()
}

case class Symm( p1: CongruenceProof ) extends CongruenceProof {
  val ( lhs, rhs ) = ( p1.rhs, p1.lhs )

  override def immediateSubProofs = Seq( p1 )
}
object Symm {
  def ifNecessary( p1: CongruenceProof ): CongruenceProof =
    p1 match {
      case Refl( _ )                => p1
      case ACTheory( op, lhs, rhs ) => ACTheory( op, rhs, lhs )
      case _                        => Symm( p1 )
    }
}

case class Trans( p1: CongruenceProof, p2: CongruenceProof ) extends CongruenceProof {
  require( p1.rhs == p2.lhs )
  val ( lhs, rhs ) = ( p1.lhs, p2.rhs )

  override def immediateSubProofs = Seq( p1, p2 )
}
object Trans {
  def ifNecessary( p1: CongruenceProof, p2: CongruenceProof ): CongruenceProof =
    ( p1, p2 ) match {
      case ( Refl( _ ), _ ) => p2
      case ( _, Refl( _ ) ) => p1
      case ( _, _ )         => Trans( p1, p2 )
    }
}

// unchecked for speed
case class ACTheory( op: Const, lhs: Expr, rhs: Expr ) extends CongruenceProof {
  override def immediateSubProofs = Seq()
}
case class ACRw( op: Const, lhs: Expr, rhs: Expr, p1: CongruenceProof ) extends CongruenceProof {
  override def immediateSubProofs = Seq( p1 )
}

case class LeftUnit( op: Const, unit: Expr, e: Expr ) extends CongruenceProof {
  val ( lhs, rhs ) = ( op( unit, e ), e )

  override def immediateSubProofs = Seq()
}
case class RightUnit( op: Const, unit: Expr, e: Expr ) extends CongruenceProof {
  val ( lhs, rhs ) = ( op( e, unit ), e )

  override def immediateSubProofs = Seq()
}

case class FOCongruence( f: Expr, as: Seq[CongruenceProof] ) extends CongruenceProof {
  val lhs = f( as.map( _.lhs ) )
  val rhs = f( as.map( _.rhs ) )

  override def immediateSubProofs = as
  override def productArity: Int = 1 + as.size
  override def productElement( n: Int ): Object = if ( n == 0 ) f else as( n - 1 )
}