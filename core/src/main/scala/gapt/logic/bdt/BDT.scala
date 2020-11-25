package gapt.logic.bdt

import gapt.logic.bdt.BDT.F
import gapt.logic.bdt.BDT.Ite
import gapt.logic.bdt.BDT.T
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.logic.Polarity
import gapt.proofs.Sequent
import gapt.provers.congruence.CC

sealed trait BDT {
  private def simp( assg: Map[Atom, Boolean], withEq: Boolean ): BDT =
    this match {
      case Ite( c, a, b ) =>
        ( assg.get( c ) match {
          case None if withEq =>
            val seq = Sequent( assg.view.mapValues( v => Polarity( !v ) ).toMap )
            if ( CC.isValid( seq :+ c ).isDefined )
              Some( true )
            else if ( CC.isValid( c +: seq ).isDefined )
              Some( false )
            else
              None
          case v => v
        } ) match {
          case Some( true ) =>
            a.simp( assg, withEq )
          case Some( false ) =>
            b.simp( assg, withEq )
          case None =>
            ( a.simp( assg + ( c -> true ), withEq ), b.simp( assg + ( c -> false ), withEq ) ) match {
              case ( T, T )   => T
              case ( F, F )   => F
              case ( a_, b_ ) => Ite( c, a_, b_ )
            }
        }
      case T => T
      case F => F
    }

  def simp: BDT = simp( Map.empty, withEq = false )
  def simpEq: BDT = simp( Map.empty, withEq = true )

  def map( f: Boolean => BDT ): BDT =
    this match {
      case Ite( c, a, b ) => Ite( c, a.map( f ), b.map( f ) )
      case T              => f( true )
      case F              => f( false )
    }

  def unary_- : BDT = map { case true => F case false => T }
  def &( that: BDT ): BDT = map { case true => that case false => F }.simp
  def |( that: BDT ): BDT = map { case true => T case false => that }.simp
  def ->:( that: BDT ): BDT = that.map { case true => this case false => T }.simp

  def toFormula: Formula =
    this match {
      case Ite( c, T, F ) => c
      case Ite( c, F, T ) => -c
      case Ite( c, T, b ) => c | b.toFormula
      case Ite( c, a, T ) => c --> a.toFormula
      case Ite( c, F, b ) => -c & b.toFormula
      case Ite( c, a, F ) => c & a.toFormula
      case Ite( c, a, b ) => ( c --> a.toFormula ) & ( c | b.toFormula )
      case T              => Top()
      case F              => Bottom()
    }

}

object BDT {
  def apply( f: Formula ): BDT = f match {
    case Top()       => T
    case Bottom()    => F
    case Neg( a )    => -apply( a )
    case And( a, b ) => apply( a ) & apply( b )
    case Or( a, b )  => apply( a ) | apply( b )
    case Imp( a, b ) => apply( a ) ->: apply( b )
    case f: Atom     => Ite( f, T, F )
  }

  case class Ite( c: Atom, a: BDT, b: BDT ) extends BDT
  case object T extends BDT
  case object F extends BDT
}
