package at.logic.gapt.formats.babel

import scalaz._
import Scalaz._

import at.logic.gapt.{ expr => real }

object ast {

  class TypeVarIdx {
    override def toString = Integer toHexString hashCode()
  }
  def gensym() = new TypeVarIdx

  sealed trait Type
  case class BaseType( name: String ) extends Type
  case class ArrType( a: Type, b: Type ) extends Type
  case class TypeVar( idx: TypeVarIdx ) extends Type
  def freshTypeVar() = TypeVar( gensym() )

  sealed trait Expr
  case class TypeAscription( expr: Expr, ty: Type ) extends Expr
  case class Ident( name: String, ty: Type ) extends Expr
  case class Abs( v: Ident, sub: Expr ) extends Expr
  case class App( a: Expr, b: Expr ) extends Expr

  def readable( t: Type ): String = t match {
    case BaseType( name ) => name
    case ArrType( a, b )  => s"(${readable( a )}>${readable( b )})"
    case TypeVar( idx )   => s"_$idx"
  }
  def readable( e: Expr ): String = e match {
    case TypeAscription( expr, ty ) => s"(${readable( expr )}:${readable( ty )})"
    case Ident( name, ty )          => s"($name:${readable( ty )})"
    case Abs( v, sub )              => s"(\\${readable( v )} ${readable( sub )})"
    case App( a, b )                => s"(${readable( a )} ${readable( b )})"
  }

  def Bool = BaseType( "o" )

  def Eq( a: Expr, b: Expr ) = {
    val argType = freshTypeVar()
    val eqType = ArrType( argType, ArrType( argType, Bool ) )
    App( App( Ident( real.EqC.name, eqType ), a ), b )
  }

  def Top = Ident( real.TopC.name, Bool )
  def Bottom = Ident( real.BottomC.name, Bool )

  def UnaryConn( name: String ): Expr => Expr = a => App( Ident( name, ArrType( Bool, Bool ) ), a )
  def Neg = UnaryConn( real.NegC.name )

  def BinaryConn( name: String ): ( Expr, Expr ) => Expr = ( a, b ) =>
    App( App( Ident( name, ArrType( Bool, ArrType( Bool, Bool ) ) ), a ), b )
  def And = BinaryConn( real.AndC.name )
  def Or = BinaryConn( real.OrC.name )
  def Bicond( a: Expr, b: Expr ) = And( Imp( a, b ), Imp( b, a ) )
  def Imp = BinaryConn( real.ImpC.name )

  def Quant( name: String ): ( Ident, Expr ) => Expr = ( v, sub ) =>
    App( Ident( name, ArrType( ArrType( freshTypeVar(), Bool ), Bool ) ), Abs( v, sub ) )
  def Ex: ( Ident, Expr ) => Expr = Quant( real.ExistsC.name )
  def All = Quant( real.ForallC.name )

  def freeVars( t: Type ): Set[TypeVarIdx] = t match {
    case BaseType( name ) => Set()
    case ArrType( a, b )  => freeVars( a ) union freeVars( b )
    case TypeVar( idx )   => Set( idx )
  }
  def subst( t: Type, assg: Map[TypeVarIdx, Type] ): Type = t match {
    case BaseType( _ )   => t
    case ArrType( a, b ) => ArrType( subst( a, assg ), subst( b, assg ) )
    case TypeVar( idx )  => assg.get( idx ).fold( t )( subst( _, assg ) )
  }
  type UnificationError = String
  def solve( eqs: List[( Type, Type )], assg: Map[TypeVarIdx, Type] ): UnificationError \/ Map[TypeVarIdx, Type] = eqs match {
    case Nil => assg.right
    case ( first :: rest ) => first match {
      case ( ArrType( a1, b1 ), ArrType( a2, b2 ) ) =>
        solve( ( a1 -> a2 ) :: ( b1 -> b2 ) :: rest, assg )
      case ( BaseType( n1 ), BaseType( n2 ) ) if n1 == n2 => solve( rest, assg )
      case ( t1 @ TypeVar( i1 ), t2 ) if assg contains i1 =>
        solve( ( assg( i1 ) -> t2 ) :: rest, assg )
      case ( t1 @ TypeVar( i1 ), t2 ) =>
        val t2_ = subst( t2, assg )
        if ( t1 == t2_ )
          solve( rest, assg )
        else if ( freeVars( t2_ ) contains i1 )
          s"Cannot unify types: ${readable( t1 )} occurs in ${readable( t2_ )}".left
        else
          solve( rest, assg + ( i1 -> t2_ ) )
      case ( t1, t2: TypeVar ) => solve( ( t2 -> t1 ) :: rest, assg )
      case ( t1, t2 )          => s"Cannot unify types ${readable( t1 )} and ${readable( t2 )}".left
    }
  }

  def infer( expr: Expr, env: Map[String, Type], s0: Map[TypeVarIdx, Type] ): UnificationError \/ ( Map[TypeVarIdx, Type], Type ) =
    expr match {
      case TypeAscription( e, t ) =>
        for {
          ( s1, et ) <- infer( e, env, s0 )
          s2 <- solve( List( et -> t ), s1 )
        } yield ( s2, et )
      case Ident( n, t ) =>
        if ( env contains n )
          for ( s1 <- solve( List( env( n ) -> t ), s0 ) ) yield ( s1, t )
        else ( s0 -> t ).right
      case Abs( Ident( vn, vt ), t ) =>
        for {
          ( s1, subt ) <- infer( t, env + ( vn -> vt ), s0 )
        } yield ( s1, ArrType( vt, subt ) )
      case App( a, b ) =>
        val appType = freshTypeVar()
        for {
          ( s1, at ) <- infer( a, env, s0 )
          ( s2, bt ) <- infer( b, env, s1 )
          s3 <- solve( List( at -> ArrType( bt, appType ) ), s2 )
        } yield ( s3, appType )
    }

  val polymorphic = Set( real.EqC.name, real.ForallC.name, real.ExistsC.name )
  def freeIdentifers( expr: Expr ): Set[String] = expr match {
    case TypeAscription( e, ty ) => freeIdentifers( e )
    case Ident( name, ty )       => Set( name )
    case Abs( v, sub )           => freeIdentifers( sub ) - v.name
    case App( a, b )             => freeIdentifers( a ) union freeIdentifers( b )
  }

  def toRealType( ty: Type, assg: Map[TypeVarIdx, Type] ): real.Ty = ty match {
    case BaseType( name ) => real.TBase( name )
    case ArrType( a, b )  => toRealType( a, assg ) -> toRealType( b, assg )
    case TypeVar( idx )   => toRealType( assg( idx ), assg )
  }
  def toRealExpr( expr: Expr, assg: Map[TypeVarIdx, Type], bound: Set[String] ): real.LambdaExpression = expr match {
    case TypeAscription( e, ty ) => toRealExpr( e, assg, bound )
    case expr @ Ident( name, ty ) =>
      if ( bound( name ) ) real.Var( name, toRealType( ty, assg ) )
      else real.Const( name, toRealType( ty, assg ) )
    case Abs( v @ Ident( vn, _ ), sub ) =>
      val bound_ = bound + vn
      real.Abs( toRealExpr( v, assg, bound_ ).asInstanceOf[real.Var], toRealExpr( sub, assg, bound_ ) )
    case App( a, b ) =>
      real.App( toRealExpr( a, assg, bound ), toRealExpr( b, assg, bound ) )
  }
  def toRealExpr( expr: Expr, isVar: String => Boolean ): UnificationError \/ real.LambdaExpression = {
    val fi = freeIdentifers( expr ) diff polymorphic
    val freeVars = fi filter isVar
    for ( ( assg, _ ) <- infer( expr, fi.map { _ -> freshTypeVar() }.toMap, Map() ) )
      yield toRealExpr( expr, assg.withDefaultValue( BaseType( "i" ) ), freeVars )
  }
  def toRealExpr( expr: Expr ): UnificationError \/ real.LambdaExpression =
    toRealExpr( expr, _ matches "[u-zU-Z].*" )

}
