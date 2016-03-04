package at.logic.gapt.formats.shlk

import at.logic.gapt.formats.simple.TypeParsers
import at.logic.gapt.proofs.lkOld._
import at.logic.gapt.proofs.lkOld.solve
import at.logic.gapt.proofs.lkOld.base._
import at.logic.gapt.proofs.shlk._
import at.logic.gapt.proofs.shlk.getName

import scala.util.matching.Regex
import scala.util.parsing.combinator._
import at.logic.gapt.expr.schema._
import at.logic.gapt.expr._
import java.io.InputStreamReader

import scala.collection.mutable.{ Map => MMap }

object PutPlusTogether {
  val nLine = sys.props( "line.separator" )

  def apply( iI: SchemaExpression, iC: SchemaExpression ): SchemaExpression = {
    iC match {
      case Const( n, t ) if n == "0" && t == Tindex => iI
      case SchemaFunction( n, l, t ) if getName( n ) == "schS" && t == Tindex => SchemaFunction( n, List( apply( iI, l.head ) ) )
      case _ => throw new Exception( "Why?" + nLine + iC.toString + nLine )
    }
  }
}
object maketogether {
  def apply( i: Int ): SchemaExpression = {
    i match {
      case 0 => Const( "0", Tindex )
      case x => {
        val param = apply( x - 1 )
        val head = Const( "schS", param.exptype -> Tindex )
        SchemaFunction( head, List( param ) )
      }
    }
  }
}

object backToInt {
  val nLine = sys.props( "line.separator" )

  def apply( i: SchemaExpression ): Int = {
    i match {
      case Const( n, t ) if n == "0" && t == Tindex => 0
      case SchemaFunction( n, l, t ) if getName( n ) == "schS" && t == Tindex => 1 + apply( l.head )
      case _ => throw new Exception( "Why?" + nLine + i.toString + nLine )
    }
  }
}
