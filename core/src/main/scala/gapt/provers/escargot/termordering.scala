package gapt.provers.escargot

import gapt.expr._
import gapt.expr.ty.Ty
import gapt.expr.ty.arity

import scala.collection.mutable

trait TermOrdering {
  def lt( e1: Expr, e2: Expr ): Boolean = lt( e1, e2, treatVarsAsConsts = false )
  def lt( e1: Expr, e2: Expr, treatVarsAsConsts: Boolean ): Boolean
}

case class LPO( precedence: Seq[String] = Seq(), typeOrderLt: ( Ty, Ty ) => Boolean = ( _, _ ) => false ) extends TermOrdering {
  val precIdx: Map[String, Int] = precedence.zipWithIndex.toMap

  def lt( e1: Expr, e2: Expr, treatVarsAsConsts: Boolean ): Boolean = {
    def majo( s: Expr, ts: List[Expr] ): Boolean =
      ts.forall( t => lpo( s, t ) )

    def alpha( ss: List[Expr], t: Expr ): Boolean =
      ss.exists( s => s == t || lpo( s, t ) )

    def precGt( h1: Expr, h2: Expr ): Boolean =
      ( h1, h2 ) match {
        case ( c1: Const, c2: Const ) =>
          // TODO: type params?
          precIdx.getOrElse( c1.name, -1 ) > precIdx.getOrElse( c2.name, -1 )
        case ( _: Const, _: Var ) if treatVarsAsConsts => true
        case ( v1: Var, v2: Var ) if treatVarsAsConsts => v1.toString > v2.toString
        case _                                         => false
      }

    def lexMa( s: Expr, t: Expr, ss: List[Expr], ts: List[Expr] ): Boolean =
      ( ss, ts ) match {
        case ( si :: sss, ti :: tss ) =>
          if ( si == ti ) lexMa( s, t, sss, tss )
          else if ( lpo( si, ti ) ) majo( s, tss )
          else alpha( ss, t )
        case _ => false
      }

    def lpo( s: Expr, t: Expr ): Boolean = {
      if ( typeOrderLt( t.ty, s.ty ) ) return true
      val Apps( sf, sas ) = s
      val Apps( tf, tas ) = t
      if ( precGt( sf, tf ) ) majo( s, tas )
      else if ( sf == tf ) lexMa( s, t, sas, tas )
      else alpha( sas, t )
    }

    lpo( e2, e1 )
  }
}

case class KBO( precedence: Seq[Const], constWeights: Map[Const, Int] = Map() ) extends TermOrdering {
  val precIdx: Map[Const, Int] = precedence.zipWithIndex.toMap
  val varWeight = ( constWeights.filterKeys { arity( _ ) == 1 }.values.toSet + 1 ).min

  def lt( e1: Expr, e2: Expr, treatVarsAsConsts: Boolean ): Boolean = {
    val w1 = weight( e1 )
    val w2 = weight( e2 )

    if ( w1 > w2 ) return false
    if ( !treatVarsAsConsts ) if ( occs( e1 ) diff occs( e2 ) nonEmpty ) return false

    if ( w1 < w2 ) return true

    val Apps( c1, as1 ) = e1
    val Apps( c2, as2 ) = e2

    def lex( as1: List[Expr], as2: List[Expr] ): Boolean =
      ( as1, as2 ) match {
        case ( a1 :: as1_, a2 :: as2_ ) if a1 == a2 => lex( as1_, as2_ )
        case ( a1 :: as1_, a2 :: as2_ ) if lt( a1, a2, treatVarsAsConsts ) => true
        case _ => false
      }

    val precLt = ( c1, c2 ) match {
      case ( c1: Const, c2: Const )                  => precIdx.getOrElse( c1, -1 ) < precIdx.getOrElse( c2, -1 )
      case ( _: Var, _: Const ) if treatVarsAsConsts => true
      case ( v1: Var, v2: Var ) if treatVarsAsConsts => v1.toString < v2.toString
      case _                                         => false
    }

    if ( precLt ) true
    else if ( c1 == c2 ) lex( as1, as2 )
    else false
  }

  def occs( expr: Expr ): Seq[Var] = {
    val r = Seq.newBuilder[Var]
    def f( e: Expr ): Unit = e match {
      case App( a, b ) =>
        f( a ); f( b )
      case v: Var => r += v
      case _      =>
    }
    f( expr )
    r.result()
  }

  def weight( expr: Expr ): Int = expr match {
    case c: Const           => constWeights.getOrElse( c, 1 )
    case v: Var             => varWeight
    case Apps( head, args ) => weight( head ) + args.map( weight ).sum
  }
}

